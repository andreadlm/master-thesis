import Mathlib.Tactic.Basic
import MasterThesis.LOOP.Language
import MasterThesis.SCORE.Language
import MasterThesis.Compiler.Commons

lemma eq_states_update {σ : LOOP.Store} {τ : SCORE.Store} (x : Ident) (v : ℕ) : σ =ₛ τ → σ[x ↦ v] =ₛ τ[x ↦ ↑v :: τ x] := by
  intros _ y
  cases eq_or_ne x y
  · simp [‹x = y›]
  · simpa [‹x ≠ y›] using ‹σ=ₛτ› y

lemma eq_states_INC {σ : LOOP.Store} {t : SCORE.State} {x : Ident} {v : ℕ} : σ[x ↦ v] =ₛ t → σ[x ↦ v + 1] =ₛ SCORE.eval (SCORE.Com.INC x) t := by
  intro
  cases t
  case some τ _ =>
    rw [SCORE.eval]
    simp only [←‹some (σ[x ↦ v]) =ₛ some τ› x]
    intro y
    cases eq_or_ne x y
    · simp [‹x = y›]
    · simpa [‹x ≠ y›] using ‹some (σ[x ↦ v]) =ₛ some τ› y
  case none =>
    contradiction

lemma eq_states_idents_subs {s : LOOP.State} {t : SCORE.State} {a b : Finset Ident} : s =[a ∪ b]ₛ t → s =[a]ₛ t := by sorry
