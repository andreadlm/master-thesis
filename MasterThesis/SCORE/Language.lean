import Mathlib.Data.Prod.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate

import MasterThesis.Commons

namespace SCORE

def Store : Type := Ident → List Int

namespace Store

def emp : Store := fun _ => []

def update (x : Ident) (l : List Int) (σ : Store) : Store :=
  fun (y : Ident) => if x = y then l else (σ y)

-- TODO: Migliorabile?
notation:100 "[" x:100 " ↦ " l:100 "]" s:100 => update x l s
notation:100 "[" x:100 " ↦ " l:100 "]"       => [x ↦ l] emp

#eval (["z" ↦ [3]] ["y" ↦ [2]] ["x" ↦ [1]]) "x"

@[simp]
lemma update_same {σ : Store} {x y : Ident} {l : List Int} : x = y → (update x l σ) y = l := by
  intros; simp only [if_pos ‹x = y›, update]

@[simp]
lemma update_other {σ : Store} {x y : Ident} {l : List Int} : x ≠ y → (update x l σ) y = σ y := by
  intros; simp only [if_neg ‹x ≠ y›, update]

lemma update_shrink {σ : Store} {x : Ident} {l₁ l₂ : List Int} : (update x l₂ (update x l₁ σ)) = update x l₂ σ := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => simp only [update_same ‹x = y›]
  | inr /- x ≠ y -/ => simp only [update_other ‹x ≠ y›]

lemma update_unchanged {σ : Store} {x : Ident} : update x (σ x) σ = σ := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => rewrite [‹x = y›]; simp only [update_same]
  | inr /- x ≠ y -/ => simp only [update_other ‹x ≠ y›]

lemma update_unchanged_cons {σ : Store} {x : Ident} {v : Int} : (σ x).head? = some v → update x (v :: (σ x).tail) σ = σ := by
  intro
  funext y
  cases eq_or_ne x y with
  | inl /- x = y-/ =>
    rw [← ‹x = y›]
    have : ([x ↦ (v :: (σ x).tail)] σ) x = (v :: (σ x).tail) := by
      { simp [‹x = y›]}; rw [this]
    have : v ∈ (σ x).head? := by
      { rw [Option.mem_def]; assumption }
    exact List.cons_head?_tail ‹v ∈ (σ x).head?›
  | inr /- x ≠ y-/ =>
    have : ([x ↦ (v :: (σ x).tail)] σ) y = σ y := by
      { simp [‹x ≠ y›] }; rw [this]

end Store

inductive State : Type :=
| prog : Store → State
| fail

notation "⊥" => State.fail

namespace State

lemma prog_or_bot (s : State) : (∃ (σ : Store), s = prog σ) ∨ s = ⊥ := by
  cases s
  case prog σ => left; exact ⟨σ, rfl⟩
  case fail   => right; rfl

end State

inductive Com : Type
| SKIP : Com
| CON  : Ident → Com
| NOC  : Ident → Com
| DEC  : Ident → Com
| INC  : Ident → Com
| SEQ  : Com → Com → Com
| FOR  : Ident → Com → Com

open Com

infixl:80 ";;" => SEQ

def comToString (indLv : Nat) (P : Com) : String :=
  let ind : String := (String.append "  ")^[indLv] ""
  match P with
  | SKIP    => s!"{ind}SKIP"
  | CON x   => s!"{ind}CON {x}"
  | NOC x   => s!"{ind}NOC {x}"
  | DEC x   => s!"{ind}DEC {x}"
  | INC x   => s!"{ind}INC {x}"
  | SEQ P Q => s!"{comToString indLv P}\n{comToString indLv Q}"
  | FOR x P => s!"{ind}FOR {x}\n{comToString (indLv + 1) P}"

instance : ToString Com where
  toString := comToString 0

#eval (SEQ (FOR "x" (SEQ (SEQ (CON "x") (FOR "x" (SEQ (CON "x") (NOC "y")))) (INC "x"))) (DEC "x"))

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

theorem inv_inv (P : Com) : (inv (inv P)) = P := by
  induction  P
  case SKIP        => simp[inv]
  case CON         => simp[inv]
  case NOC         => simp[inv]
  case DEC         => simp[inv]
  case INC         => simp[inv]
  case SEQ ih₁ ih₂ => simp[inv, ih₁, ih₂]
  case FOR ih      => simp[inv, ih]

end SCORE
