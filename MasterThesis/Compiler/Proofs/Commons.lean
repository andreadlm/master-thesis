import Mathlib.Tactic.Basic
import MasterThesis.SCORE.Interpreter
import MasterThesis.SCORE.Proofs.Language
import MasterThesis.LOOP.Proofs.Language
import MasterThesis.Compiler.Commons

lemma eq_states_update {σ : LOOP.Store} {τ : SCORE.Store} (x : Ident) (v : ℕ) : some σ =ₛ some τ → some ([x ↦ v] σ) =ₛ some ([x ↦ ↑v :: τ x] τ) := by
  intros _ y
  cases eq_or_ne x y
  · simp [‹x = y›]
  · simpa [‹x ≠ y›] using ‹σ=ₛτ› y

lemma eq_states_INC {σ : LOOP.Store} {t : SCORE.State} {x : Ident} {v : ℕ} : some ([x ↦ v] σ) =ₛ t → some ([x ↦ v + 1] σ) =ₛ SCORE.eval (SCORE.Com.INC x) t := by
  intro
  cases t
  case some τ _ =>
    rw [SCORE.eval]
    simp only [←‹some ([x ↦ v] σ) =ₛ some τ› x]
    intro y
    cases eq_or_ne x y
    · simp [‹x = y›]
    · simpa [‹x ≠ y›] using ‹some ([x ↦ v] σ) =ₛ some τ› y
  case none =>
    contradiction
