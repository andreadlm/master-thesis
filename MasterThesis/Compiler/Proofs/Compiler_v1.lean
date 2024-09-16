import Mathlib.Tactic.Basic
import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language
import MasterThesis.Compiler.Compiler_v1
import MasterThesis.Compiler.Proofs.Commons

namespace Compiler

theorem soundness {s : LOOP.State} {t : SCORE.State} (P : LOOP.Com) : s =ₛ t → (LOOP.eval P s) =ₛ (SCORE.eval (l2s P) t) := by
  intro eqs
  induction P generalizing s t
  all_goals (cases s <;> cases t)
  case SKIP.some.some =>
    rwa [LOOP.eval, l2s, SCORE.eval]
  case ZER.some.some x σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    intro y
    cases eq_or_ne x y
    · simp [‹x = y›]
    · simpa [‹x ≠ y›] using ‹σ =ₛ τ› y
  case ASN.some.some x y σ τ =>
    rw [LOOP.eval]
    cases eq_or_ne x y
    · rw [l2s]
      simpa [‹x = y›, SCORE.eval]
    · have : SCORE.eval (l2s (LOOP.Com.ASN x y)) (some τ) = (fun τ ↦ SCORE.eval (SCORE.Com.INC x) τ)^[σ y] (some (τ[x ↦ 0 :: τ x])) := by
        rw [l2s]
        simp [‹x ≠ y›, SCORE.eval, ←(‹σ =ₛ τ› y)]
      rw [this]; clear this
      induction (σ y)
      case zero =>
        simpa using eq_states_update x 0 ‹some σ =ₛ some τ›
      case succ m ih =>
        simpa [Nat.add_comm m 1, Function.iterate_add_apply] using eq_states_INC ih
  case INC.some.some x σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    split
    · intro y
      cases eq_or_ne x y
      · simpa [‹x = y›, ←‹σ =ₛ τ› y] using ‹(τ x).head? = some _›
      · simpa [‹x ≠ y›] using ‹σ =ₛ τ› y
    · simp [←‹some σ =ₛ some τ› x] at ‹(τ x).head? = none›
  case SEQ.some.some LQ LR ih₁ ih₂ σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    exact ih₂ (ih₁ ‹σ =ₛ τ›)
  case LOOP.some.some x LQ ih σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    split
    · simp only [←(Option.some_inj.mp (Eq.trans (‹σ =ₛ τ› x) ‹(τ x).head? = some _›))]
      generalize some σ = s, some τ = t at ‹some σ =ₛ some τ›
      induction σ x generalizing s t
      case zero =>
        simpa
      case succ _ ih₂ =>
        exact ih₂ (LOOP.eval LQ s) (SCORE.eval (l2s LQ) t) (ih ‹s =ₛ t›)
    · simp [←‹some σ =ₛ some τ› x] at ‹(τ x).head? = none›
  all_goals (simp only [eq_states] at eqs)

end Compiler
