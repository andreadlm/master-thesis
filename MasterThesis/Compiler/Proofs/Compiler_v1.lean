import Mathlib.Tactic.Basic
import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language
import MasterThesis.Compiler.Compiler_v1
import MasterThesis.Compiler.Proofs.Commons

namespace Compiler

theorem soundness {s : LOOP.State} {t : SCORE.State} (P : LOOP.Com) : s ∼ t → (LOOP.eval P s) ∼ (SCORE.eval (l2s P) t) := by
  intro eqs
  induction P generalizing s t
  all_goals (cases s <;> cases t)
  case SKIP.some.some σ τ =>
    rwa [LOOP.eval, l2s, SCORE.eval]
  case ZER.some.some x σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    exact eq_states_update x 0 ‹σ ∼ τ›
  case ASN.some.some x y σ τ =>
    rw [LOOP.eval]
    cases eq_or_ne x y
    · simpa [l2s, ‹x = y›, SCORE.eval]
    · have : SCORE.eval (l2s (.ASN x y)) τ = (fun τ ↦ SCORE.eval (.INC x) τ)^[σ y] (τ[x ↦ 0 :: τ x]) := by
        simp [l2s, ‹x ≠ y›, SCORE.eval, ←(‹σ ∼ τ› y)]
      rw [this]; clear this
      induction (σ y)
      case zero =>
        simpa using eq_states_update x 0 ‹σ ∼ τ›
      case succ m ih =>
        simpa [Nat.add_comm m 1, Function.iterate_add_apply] using eq_states_INC ih
  case INC.some.some x σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    split
    · intro y
      cases eq_or_ne x y
      · simpa [‹x = y›, ←‹σ ∼ τ› y] using ‹(τ x).head? = some _›
      · simpa [‹x ≠ y›] using ‹σ ∼ τ› y
    · simp [←‹σ ∼ τ› x] at ‹(τ x).head? = none›
  case SEQ.some.some P Q ih₁ ih₂ σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    exact ih₂ (ih₁ ‹σ ∼ τ›)
  case LOOP.some.some x LQ ih σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    split
    · simp only [←(Option.some_inj.mp (Eq.trans (‹σ ∼ τ› x) ‹(τ x).head? = some _›))]
      generalize some σ = s, some τ = t at ‹σ ∼ τ›
      induction σ x generalizing s t
      case zero =>
        simpa
      case succ _ ih₂ =>
        exact ih₂ (LOOP.eval LQ s) (SCORE.eval (l2s LQ) t) (ih ‹s ∼ t›)
    · simp [←‹σ ∼ τ› x] at ‹(τ x).head? = none›
  all_goals (simp only [eq_states] at eqs)

end Compiler
