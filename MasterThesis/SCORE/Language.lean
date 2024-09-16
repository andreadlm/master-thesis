/-
"A LEAN-certified reversibilization of Meyer-Ritchie LOOP language".
Master thesis in computer science, University of Turin.
Authors: Andrea Delmastro
-/
import Mathlib.Data.Prod.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import MasterThesis.Commons

/-!
# SCORE language

This file defines SCORE, a minimal reversible programming language designed as a reversible
adaptation of LOOP. SCORE can be understood as an extension of SRL [Matos:SRL] that operates on variables
represented by stacks of integers.

## Notations

* `[x ↦ v]` stands for `update emp x v` where `emp` is the empty `Store` (_set the value of_ `x` _to_ `v` _in_ `emp`).
* `σ[x ↦ v]` stands for `update σ x v` (_set the value of_ `x` _to_ `v` _in_ `σ`).

Consecutive updates can be concatenated as `σ[x ↦ v₁][x ↦ v₂]`.

* `P⁻¹` stands for `inv P` (_the inverse program of_ `P`).
-/

namespace SCORE

/-- A `Store` provides an abstract representation of memory in the form of a total function from
`Ident` to `List Int`. -/
def Store : Type := Ident → List Int

namespace Store

/-- An empty `Store` maps every identifier to the empty list. -/
def emp : Store := fun _ => []

/-- Updates a `Store` by mapping the register identified by `x` to a new value `v`. -/
def update (σ : Store) (x : Ident) (l : List Int) : Store :=
  fun (y : Ident) => if x = y then l else (σ y)

notation:65 "[" x:65 " ↦ " l:65 "]"      => update emp x l
notation:65 σ:65 "[" x:65 " ↦ " l:65 "]" => update σ x l

/-- If `x = y` then the current value of `y` in `σ[x ↦ v]` is `v`. -/
@[simp] lemma update_same {σ : Store} {x y : Ident} {l : List Int} : x = y → (σ[x ↦ l]) y = l := by
  intros; simp only [if_pos ‹x = y›, update]

/-- If `x ≠ y` then the current value of `y` in `σ[x ↦ v]` is `σ y`. -/
@[simp] lemma update_other {σ : Store} {x y : Ident} {l : List Int} : x ≠ y → (σ[x ↦ l]) y = σ y := by
  intros; simp only [if_neg ‹x ≠ y›, update]

/-- Updating a variable to its current value produces no change. -/
@[simp] lemma update_unchanged {σ : Store} {x : Ident} : σ[x ↦ (σ x)] = σ := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => rewrite [‹x = y›]; simp only [update_same]
  | inr /- x ≠ y -/ => simp only [update_other ‹x ≠ y›]

/-- Two consecutive updates to the same variable can be _compressed_ into a single update. -/
@[simp] lemma update_shrink {σ : Store} {x : Ident} {l₁ l₂ : List Int} : σ[x ↦ l₁][x ↦ l₂] = σ[x ↦ l₂] := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => simp only [update_same ‹x = y›]
  | inr /- x ≠ y -/ => simp only [update_other ‹x ≠ y›]

/-- Alternative version of `update_unchanged` that considers the structure of the list. -/
lemma update_unchanged_cons {σ : Store} {x : Ident} {v : Int} : (σ x).head? = v → σ[x ↦ (v :: (σ x).tail)] = σ := by
  intro
  simpa (config := { singlePass := true })
    only [List.eq_cons_of_mem_head? ‹(σ x).head? = v›]
    using @update_unchanged σ x

end Store

/-- A `State` can be a `Store` or a failure. -/
abbrev State := Option Store

namespace State

notation "⊥" => (none : State)

end State

/-- A SCORE program is a sequence of commands chosen from skip, extending a stack, decreasing a
stack, incrementing the top of a stack, decrementing the top of a stack, composing two commands, and
iterating over a finite number of steps. -/
inductive Com : Type
| SKIP : Com
| CON  : Ident → Com
| NOC  : Ident → Com
| DEC  : Ident → Com
| INC  : Ident → Com
| SEQ  : Com → Com → Com
| FOR  : Ident → Com → Com
deriving BEq

namespace Com

infixr:80 ";;" => SEQ

/-- Computes the string representation of a LOOP command. -/
def comToString (indLv : Nat) (P : Com) : String :=
  let rec ind (indLv : Nat) : String :=
    match indLv with
    | .zero   => ""
    | .succ m => "  " ++ ind m
  match P with
  | SKIP    => s!"{ind indLv}SKIP"
  | CON x   => s!"{ind indLv}CON {x}"
  | NOC x   => s!"{ind indLv}NOC {x}"
  | DEC x   => s!"{ind indLv}DEC {x}"
  | INC x   => s!"{ind indLv}INC {x}"
  | SEQ P Q => s!"{comToString indLv P};\n{comToString indLv Q}"
  | FOR x P => s!"{ind indLv}FOR {x} \{\n{comToString (indLv + 1) P}\n{ind indLv}}"

instance : ToString Com where
  toString := comToString 0

end Com

open Com

/-  Program inverter for SCORE. Computes the inverse of a SCORE program. -/
def inv (P : Com) : Com :=
  match P with
  | SKIP    => SKIP
  | CON x   => NOC x
  | NOC x   => CON x
  | DEC x   => INC x
  | INC x   => DEC x
  | SEQ P Q => SEQ (inv Q) (inv P)
  | FOR x Q => FOR x (inv Q)

postfix:max "⁻¹" => inv

/-- The inverse of the inverse program of `P` is `P` itself. -/
theorem inv_inv (P : Com) : (inv (inv P)) = P := by
  induction  P
  case SKIP        => simp[inv]
  case CON         => simp[inv]
  case NOC         => simp[inv]
  case DEC         => simp[inv]
  case INC         => simp[inv]
  case SEQ ih₁ ih₂ => simp[inv, ih₁, ih₂]
  case FOR ih      => simp[inv, ih]

mutual
  /-- Interpreter for SCORE. The interpreter takes as input a `Com` and an evaluation `State` and
  outputs the resulting `State` obtained by applying the command to the initial state. -/
  def eval (P : Com) (s : State) : State :=
    match s with
    | ⊥      => ⊥
    | some σ =>
      match P with
      | SKIP    => s
      | CON x   => σ[x ↦ (0 :: (σ x))]
      | NOC x   => match (σ x).head? with
                   | some 0 => σ[x ↦ (σ x).tail]
                   | _      => ⊥
      | DEC x   => match (σ x).head? with
                   | some v => σ[x ↦ ((v - 1) :: (σ x).tail)]
                   | none   => ⊥
      | INC x   => match (σ x).head? with
                   | some v => σ[x ↦ ((v + 1) :: (σ x).tail)]
                   | none   => ⊥
      | SEQ P Q => (eval Q) (eval P s)
      | FOR x P => match (σ x).head? with
                   | some v => match v with
                               | Int.ofNat   k => (fun t => eval  P t)^[k] s
                               | Int.negSucc k => (fun t => evalI P t)^[k.succ] s
                   | none   => ⊥
  /-- Reverse interpreter for SCORE. The interpreter takes as input a `Com` and an evaluation `State`
  and outputs the resulting `State` obtained by applying the inverse of the command to the initial
  state. -/
  def evalI (P : Com) (s : State) : State :=
    match s with
    | ⊥      => ⊥
    | some σ =>
      match P with
      | SKIP    => s
      | CON x   => match (σ x).head? with
                   | some 0 => σ[x ↦ (σ x).tail]
                   | _   => ⊥
      | NOC x   => σ [x ↦ (0 :: (σ x))]
      | DEC x   => match (σ x).head? with
                   | some v => σ[x ↦ ((v + 1) :: (σ x).tail)]
                   | none   => ⊥
      | INC x   => match (σ x).head? with
                   | some v => σ[x ↦ ((v - 1) :: (σ x).tail)]
                   | none   => ⊥
      | SEQ P Q => (evalI Q) (evalI P s)
      | FOR x P => match (σ x).head? with
                   | some v => match v with
                               | Int.ofNat   k => (fun t => evalI P t)^[k] s
                               | Int.negSucc k => (fun t => eval  P t)^[k.succ] s
                   | none   => ⊥
end

end SCORE
