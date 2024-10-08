/-
"A Lean-certified reversibilization of Meyer-Ritchie LOOP language".
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
@[simp] lemma update_no_update {σ : Store} {x : Ident} : σ[x ↦ (σ x)] = σ := by
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

/-- Alternative version of `update_no_update` that considers the structure of the list. -/
lemma update_no_update_cons {σ : Store} {x : Ident} {v : Int} : (σ x).head? = v → σ[x ↦ (v :: (σ x).tail)] = σ := by
  intro
  simpa (config := { singlePass := true })
    only [List.eq_cons_of_mem_head? ‹(σ x).head? = v›]
    using @update_no_update σ x

/-- The order in which two different variables are updated is not significant.  -/
lemma update_swap {σ : Store} {x y : Ident} {l₁ l₂ : List Int} : x ≠ y → σ[x ↦ l₁][y ↦ l₂] = σ[y ↦ l₂][x ↦ l₁] := by
  intro
  funext z
  cases eq_or_ne x z with
  | inl /- x = z -/ =>
    cases eq_or_ne y z with
    | inl /- y = z -/ =>
      have := Eq.trans ‹x = z› ‹y = z›.symm
      contradiction
    | inr /- y ≠ z -/ => simp [‹y ≠ z›, ‹x = z›]
  | inr /- x ≠ z -/ =>
    cases eq_or_ne y z with
    | inl /- y = z -/ => simp [‹y = z›, ‹x ≠ z›]
    | inr /- y ≠ z -/ => simp [‹y ≠ z›, ‹x ≠ z›]

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

open Store Com

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
theorem inv_inv (P : Com) : inv (inv P) = P := by
  induction  P
  case SKIP        => simp[inv]
  case CON         => simp[inv]
  case NOC         => simp[inv]
  case DEC         => simp[inv]
  case INC         => simp[inv]
  case SEQ ih₁ ih₂ => simp[inv, ih₁, ih₂]
  case FOR ih      => simp[inv, ih]

/-! ### Interpreter -/

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
      | SEQ P Q => (evalI P) (evalI Q s)
      | FOR x P => match (σ x).head? with
                   | some v => match v with
                               | Int.ofNat   k => (fun t => evalI P t)^[k] s
                               | Int.negSucc k => (fun t => eval  P t)^[k.succ] s
                   | none   => ⊥
end

/-! ### Invertibility -/

lemma invertible_SKIP {s t : State} : eval SKIP s = t ∧ t ≠ ⊥ ↔ eval SKIP⁻¹ t = s ∧ s ≠ ⊥ := by
  constructor
  case mp =>
    intro
    have ⟨_, _⟩ := ‹eval SKIP s = t ∧ t ≠ ⊥›
    match s with
    | some σ =>
      constructor
      · rw [eval] at ‹eval SKIP σ = t›
        simp [inv, ←‹σ = t›, eval]
      · exact Option.some_ne_none σ
    | ⊥ =>
      rw [eval] at ‹eval SKIP ⊥ = t›
      symm at ‹⊥ = t›
      contradiction
  case mpr =>
    intro
    have ⟨_, _⟩ := ‹eval SKIP⁻¹ t = s ∧ s ≠ ⊥›
    match t with
    | some σ =>
      constructor
      · rw [inv, eval] at ‹eval SKIP⁻¹ σ = s›
        simp [←‹σ = s›, eval]
      · exact Option.some_ne_none σ
    | ⊥ =>
      rw [inv, eval] at ‹eval SKIP⁻¹ ⊥ = s›
      symm at ‹⊥ = s›
      contradiction

lemma invertible_CON {s t : State} {x : Ident} : eval (CON x) s = t ∧ t ≠ ⊥ ↔ eval (CON x)⁻¹ t = s ∧ s ≠ ⊥ := by
  constructor
  case mp =>
    intro
    have ⟨_, _⟩ := ‹eval (CON x) s = t ∧ t ≠ ⊥›
    clear ‹eval (CON x) s = t ∧ t ≠ ⊥›
    match s with
    | some σ =>
      constructor
      · rw [eval] at ‹eval (CON x) σ = t›
        simp [inv, ←‹σ[x ↦ 0 :: σ x] = t›, eval]
      · exact Option.some_ne_none σ
    | ⊥ =>
      rw [eval] at ‹eval (CON x) ⊥ = t›
      symm at ‹⊥ = t›
      contradiction
  case mpr =>
    intro
    have ⟨lh, _⟩ := ‹eval (CON x)⁻¹ t = s ∧ s ≠ ⊥›
    clear ‹eval (CON x)⁻¹ t = s ∧ s ≠ ⊥›
    match t with
    | some σ =>
      constructor
      · rw [inv, eval] at ‹eval (CON x)⁻¹ σ = s›
        split at lh
        · rw [←‹σ[x ↦ (σ x).tail] = s›, eval]
          simp [update_no_update_cons ‹(σ x).head? = some 0›]
        · symm at ‹⊥ = s›
          contradiction
      · exact Option.some_ne_none σ
    | ⊥ =>
      rw [inv, eval] at ‹eval (CON x)⁻¹ ⊥ = s›
      symm at ‹⊥ = s›
      contradiction

lemma invertible_NOC {s t : State} {x : Ident} : eval (NOC x) s = t ∧ t ≠ ⊥ ↔ eval (NOC x)⁻¹ t = s ∧ s ≠ ⊥ := by
  have : NOC x = (CON x)⁻¹ := by rw [inv]
  rw [‹NOC x = (CON x)⁻¹› , inv]
  symm
  exact invertible_CON

lemma invertible_DEC {s t : State} {x : Ident} : eval (DEC x) s = t ∧ t ≠ ⊥ ↔ eval (DEC x)⁻¹ t = s ∧ s ≠ ⊥ := by
  constructor
  case mp  =>
    intro
    have ⟨lh, _⟩ := ‹eval (DEC x) s = t ∧ t ≠ ⊥›
    clear ‹eval (DEC x) s = t ∧ t ≠ ⊥›
    match s with
    | some σ =>
      constructor
      · rw [eval] at ‹eval (DEC x) σ = t›
        split at lh
        case h_1 v _ =>
          simpa [inv, ←‹σ[x ↦ (v - 1) :: (σ x).tail] = t›, eval]
            using update_no_update_cons ‹(σ x).head? = v›
        case h_2 =>
          symm at ‹⊥ = t›
          contradiction
      · exact Option.some_ne_none σ
    | ⊥ =>
      rw [eval] at ‹eval (DEC x) ⊥ = t›
      symm at ‹⊥ = t›
      contradiction
  case mpr =>
    intro
    have ⟨lh, _⟩ := ‹eval (DEC x)⁻¹ t = s ∧ s ≠ ⊥›
    clear ‹eval (DEC x)⁻¹ t = s ∧ s ≠ ⊥›
    match t with
    | some σ =>
      constructor
      · rw [inv, eval] at ‹eval (DEC x)⁻¹ σ = s›
        split at lh
        case h_1 v _ =>
          simpa [←‹σ[x ↦ ((v + 1) :: (σ x).tail)] = s›, eval]
            using update_no_update_cons ‹(σ x).head? = v›
        case h_2 =>
          symm at ‹⊥ = s›
          contradiction
      · exact Option.some_ne_none σ
    | ⊥ =>
      rw [inv, eval] at ‹eval (DEC x)⁻¹ ⊥ = s›
      symm at ‹⊥ = s›
      contradiction

lemma invertible_INC {s t : State} {x : Ident} : eval (INC x) s = t ∧ t ≠ ⊥ ↔ eval (INC x)⁻¹ t = s ∧ s ≠ ⊥ := by
  have : INC x = (DEC x)⁻¹ := by rw [inv]
  rw [‹INC x = (DEC x)⁻¹›, inv]
  symm
  exact invertible_DEC

lemma invertible_SEQ {s t : State} {P Q : Com} (ih₁ : ∀ {s t : State}, eval P s = t ∧ t ≠ ⊥ ↔ eval P⁻¹ t = s ∧ s ≠ ⊥) (ih₂ : ∀ {s t : State}, eval Q s = t ∧ t ≠ ⊥ ↔ eval Q⁻¹ t = s ∧ s ≠ ⊥) : eval (P;;Q) s = t ∧ t ≠ ⊥ ↔ eval (P;;Q)⁻¹ t = s ∧ s ≠ ⊥ := by
  constructor
  case mp =>
    intro
    have ⟨_, _⟩ := ‹eval (P;;Q) s = t ∧ t ≠ ⊥›
    clear ‹eval (P ;; Q) s = t ∧ t ≠ ⊥›
    match s, t with
    | some σ, some τ =>
      rw [inv, eval]
      rw [eval] at ‹eval (P ;; Q) σ = τ›
      have ⟨_, _⟩ := ih₂.mp ⟨‹eval Q (eval P σ) = τ›, ‹some τ ≠ ⊥›⟩
      have : eval Q⁻¹ τ ≠ ⊥ := Eq.trans_ne ‹eval Q⁻¹ τ = eval P σ› ‹eval P σ ≠ ⊥›
      exact ih₁.mp ⟨‹eval Q⁻¹ τ = eval P σ›.symm, ‹eval Q⁻¹ τ ≠ ⊥›⟩
    | ⊥, t =>
      rw [eval] at ‹eval (P;;Q) ⊥ = t›
      symm at ‹⊥ = t›
      contradiction
    | s, ⊥ =>
      contradiction
  case mpr =>
    intro
    have ⟨_, _⟩ := ‹eval (P;;Q)⁻¹ t = s ∧ s ≠ ⊥›
    clear ‹eval (P ;; Q)⁻¹ t = s ∧ s ≠ ⊥›
    match t, s with
    | some τ, some σ =>
      rw [eval]
      rw [inv, eval] at ‹eval (P;;Q)⁻¹ τ = σ›
      have ⟨_, _⟩ := ih₁.mpr ⟨‹eval P⁻¹ (eval Q⁻¹ τ) = σ›, ‹some σ ≠ ⊥›⟩
      have : eval P σ ≠ ⊥ := Eq.trans_ne ‹eval P σ = eval Q⁻¹ τ› ‹eval Q⁻¹ τ ≠ ⊥›
      exact ih₂.mpr ⟨‹eval P σ = eval Q⁻¹ τ›.symm, ‹eval P σ ≠ ⊥›⟩
    | t, ⊥ =>
      contradiction
    | ⊥, s =>
      rw [inv, eval] at ‹eval (P ;; Q)⁻¹ ⊥ = s›
      symm at ‹⊥ = s›
      contradiction

theorem invertible {s t : State} {P : Com} : eval P s = t ∧ t ≠ ⊥ ↔ eval P⁻¹ t = s ∧ s ≠ ⊥ := by
  induction P generalizing s t
  case SKIP        => exact invertible_SKIP
  case CON         => exact invertible_CON
  case NOC         => exact invertible_NOC
  case DEC         => exact invertible_DEC
  case INC         => exact invertible_INC
  case SEQ ih₁ ih₂ => exact invertible_SEQ ih₁ ih₂
  case FOR x P     => sorry

end SCORE
