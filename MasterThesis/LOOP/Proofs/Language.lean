import Mathlib.Tactic.Basic
import Mathlib.Logic.Basic
import MasterThesis.LOOP.Language

open LOOP Store

@[simp]
lemma update_same {σ : Store} {x y : Ident} {v : Nat} : x = y → (σ[x ↦ v]) y = v := by
  intros
  unfold update
  apply if_pos
  assumption

@[simp]
lemma update_other {σ : Store} {x y : Ident} {v : Nat} : x ≠ y → (σ[x ↦ v]) y = (σ y) := by
  intros
  unfold update
  apply if_neg
  assumption

@[simp]
lemma update_no_update {σ : Store} {x : Ident} : (σ[x ↦ (σ x)]) = σ := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => rw[update_same ‹x = y›, ‹x = y›]
  | inr /- x ≠ y -/ => rw[update_other ‹x ≠ y›]
