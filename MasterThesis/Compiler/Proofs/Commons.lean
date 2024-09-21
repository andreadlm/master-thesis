import Mathlib.Tactic.Basic
import MasterThesis.LOOP.Language
import MasterThesis.SCORE.Language
import MasterThesis.Compiler.Commons

lemma eq_states_update {σ : LOOP.Store} {τ : SCORE.Store} (x : Ident) (v : ℕ) : σ ∼ τ → σ[x ↦ v] ∼ τ[x ↦ ↑v :: τ x] := by
  intros _ y
  cases eq_or_ne x y
  · simp [‹x = y›]
  · simpa [‹x ≠ y›] using ‹σ ∼ τ› y

lemma eq_states_INC {σ : LOOP.Store} {t : SCORE.State} {x : Ident} {v : ℕ} : σ[x ↦ v] ∼ t → σ[x ↦ v + 1] ∼ SCORE.eval (.INC x) t := by
  intro
  cases t
  case some τ _ =>
    rw [SCORE.eval]
    simp only [←‹σ[x ↦ v] ∼ τ› x]
    intro y
    cases eq_or_ne x y
    · simp [‹x = y›]
    · simpa [‹x ≠ y›] using ‹σ[x ↦ v] ∼ τ› y
  case none =>
    contradiction

lemma eq_states_idents_subs {s : LOOP.State} {t : SCORE.State} {a b : Finset Ident} : s =[a ∪ b]ₛ t → s =[a]ₛ t := by sorry
