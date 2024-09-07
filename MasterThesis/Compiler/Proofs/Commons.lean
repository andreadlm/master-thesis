import Mathlib.Tactic.Basic
import MasterThesis.SCORE.Interpreter
import MasterThesis.LOOP.Interpreter
import MasterThesis.SCORE.Proofs.Language
import MasterThesis.LOOP.Proofs.Language
import MasterThesis.Compiler.Commons

lemma eq_states_update {σ : LOOP.Store} {τ : SCORE.Store} (x : Ident) (v : ℕ) : some σ =ₛ some τ → some (σ[x ↦ v]) =ₛ some (τ[x ↦ ↑v :: τ x]) := by
  intros _ y
  cases eq_or_ne x y
  · simp [‹x = y›]
  · simpa [‹x ≠ y›] using ‹σ=ₛτ› y

lemma eq_states_INC {σ : LOOP.Store} {t : SCORE.State} {x : Ident} {v : ℕ} : some (σ[x ↦ v]) =ₛ t → some (σ[x ↦ v + 1]) =ₛ SCORE.eval (SCORE.Com.INC x) t := by
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
