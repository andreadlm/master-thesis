import Mathlib.Data.Prod.Basic
import Mathlib.Data.List.Basic
import MasterThesis.SCORE.Language

namespace SCORE

open SCORE Com

theorem inv_inv (P : Com) : (inv (inv P)) = P := by
  induction  P
  case SKIP        => simp[inv]
  case CON         => simp[inv]
  case NOC         => simp[inv]
  case DEC         => simp[inv]
  case INC         => simp[inv]
  case SEQ ih₁ ih₂ => simp[inv, ih₁, ih₂]
  case FOR ih      => simp[inv, ih]

namespace Store

@[simp]
lemma update_same {σ : Store} {x y : Ident} {l : List Int} : x = y → (σ[x ↦ l]) y = l := by
  intros; simp only [if_pos ‹x = y›, update]

@[simp]
lemma update_other {σ : Store} {x y : Ident} {l : List Int} : x ≠ y → (σ[x ↦ l]) y = σ y := by
  intros; simp only [if_neg ‹x ≠ y›, update]

@[simp]
lemma update_shrink {σ : Store} {x : Ident} {l₁ l₂ : List Int} : σ[x ↦ l₁][x ↦ l₂] = σ[x ↦ l₂] := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => simp only [update_same ‹x = y›]
  | inr /- x ≠ y -/ => simp only [update_other ‹x ≠ y›]

@[simp]
lemma update_unchanged {σ : Store} {x : Ident} : σ[x ↦ (σ x)] = σ := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => rewrite [‹x = y›]; simp only [update_same]
  | inr /- x ≠ y -/ => simp only [update_other ‹x ≠ y›]

lemma update_unchanged_cons {σ : Store} {x : Ident} {v : Int} : (σ x).head? = v → σ[x ↦ (v :: (σ x).tail)]= σ := by
  intro
  funext y
  cases eq_or_ne x y with
  | inl /- x = y-/ =>
    rw [← ‹x = y›]
    have : (σ[x ↦ (v :: (σ x).tail)]) x = (v :: (σ x).tail) := by
      { simp [‹x = y›]}; rw [this]
    have : v ∈ (σ x).head? := by
      { rw [Option.mem_def]; assumption }
    exact List.cons_head?_tail ‹v ∈ (σ x).head?›
  | inr /- x ≠ y-/ =>
    have : (σ[x ↦ (v :: (σ x).tail)]) y = σ y := by
      { simp [‹x ≠ y›] }; rw [this]

end Store

end SCORE
