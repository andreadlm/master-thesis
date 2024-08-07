import Mathlib.Tactic.Basic
import MasterThesis.SCORE.Proofs.Language
import MasterThesis.LOOP.Proofs.Language
import MasterThesis.SCORE.Interpreter
import MasterThesis.LOOP.Interpreter
import MasterThesis.Compiler.Compiler_v1
import MasterThesis.Compiler.Commons

namespace Compiler

lemma eq_states_update {σ : LOOP.Store} {τ : SCORE.Store} (x : Ident) (v : ℕ) : some σ =ₛ some τ → some ([x ↦ v] σ) =ₛ some ([x ↦ (Int.ofNat v :: τ x)] τ) := by sorry

lemma eq_states_INC {σ : LOOP.Store} {t : SCORE.State} {x : Ident} {v : ℕ}: some ([x ↦ v] σ) =ₛ t → some ([x ↦ (v + 1)] σ) =ₛ SCORE.eval (SCORE.Com.INC x) t := by sorry

/-
lemma eq_stores_update {σ : LOOP.Store} {τ : SCORE.Store} (x : Ident) (v : ℕ) : σ =ₛ τ → [x ↦ v]σ =ₛ [x ↦ (Int.ofNat v :: τ x)]τ := by
  intros _ y
  cases eq_or_ne x y with
  | inl /- x = y -/ =>
    have : ([x ↦ (Int.ofNat v :: τ x)]τ) y = Int.ofNat v :: τ x := by
      { simp [‹x = y›] }; rw [this]
    have : ([x ↦ v]σ) y = v := by
      { simp [‹x = y›] }; rw [this]
    have : (Int.ofNat v :: τ x).head? = Int.ofNat v := by
      { simp }; rw [this]
  | inr /- x ≠ y -/ =>
    have : ([x ↦ v]σ) y = σ y := by
      { simp [‹x ≠ y›] }; rw [this]
    have : ([x ↦ (Int.ofNat v :: τ x)]τ) y = τ y := by
      { simp [‹x ≠ y›] }; rw [this]
    exact ‹σ=ₛτ› y


lemma eq_stores_INC {σ : LOOP.Store} {τ : SCORE.Store} {x : Ident} {v : ℕ}: [x ↦ v]σ =ₛ τ → [x ↦ (v + 1)]σ =ₛ SCORE.eval (INC x) τ := by
  intros _ y
  cases eq_or_ne x y with
  | inl /- x = y -/ =>
    rw [SCORE.eval]
    have : ([x ↦ (v + 1)]σ) y = (v + 1) := by
      { simp [‹x = y›] }; rw [this]
    have : (τ x).head? = some (Int.ofNat v) := by
      { rw [← ‹[x ↦ v]σ =ₛ τ› x]
        have : ([x ↦ v]σ) x = v := by
          { simp }; rw [this]
      }; simp only [this]
    have : ([x ↦ ((Int.ofNat v + 1) :: (τ x).tail)]τ) y = ((Int.ofNat v + 1) :: (τ x).tail) := by
      { simp [‹x = y›] }; rw [this]
    have : Int.ofNat (v + 1) = Int.ofNat v + 1 := by
      { simp }; rw [this]
    rw [List.head?_cons]
  | inr /- x ≠ y -/ =>
    rw [SCORE.eval]
    have : ([x ↦ (v + 1)]σ) y = σ y := by
      { simp [‹x ≠ y›] }; rw [this]
    have : (τ x).head? = some (Int.ofNat v) := by
      { rw [← ‹[x ↦ v]σ =ₛ τ› x]
        have : ([x ↦ v]σ) x = v := by
          { simp }; rw [this]
      }; simp only [this]
    have : ([x ↦ ((Int.ofNat v + 1) :: (τ x).tail)]τ) y = τ y := by
      { simp [‹x ≠ y›] }; rw [this]
    rw [← ‹[x ↦ v]σ =ₛ τ› y]
    have : ([x ↦ v]σ) y = σ y := by
      { simp [‹x ≠ y›] }; rw [this]

-/

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
    · have : SCORE.eval (l2s (LOOP.Com.ASN x y)) (some τ) = (fun τ ↦ SCORE.eval (SCORE.Com.INC x) τ)^[σ y] (some ([x ↦ 0 :: τ x] τ)) := by
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
    · rw [←‹some σ =ₛ some τ› x] at ‹(τ x).head? = none›
      contradiction
  case SEQ.some.some LQ LR ih₁ ih₂ σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    exact ih₂ (ih₁ ‹σ =ₛ τ›)
  case FOR.some.some x LQ ih σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    split
    · simp only [←(Option.some_inj.mp (Eq.trans (‹σ =ₛ τ› x) ‹(τ x).head? = some _›))]
      generalize some σ = s, some τ = t at ‹some σ =ₛ some τ›
      induction σ x generalizing s t
      case zero =>
        simpa
      case succ _ ih₂ =>
        exact ih₂ (LOOP.eval LQ s) (SCORE.eval (l2s LQ) t) (ih ‹s =ₛ t›)
    · rw [←‹some σ =ₛ some τ› x] at ‹(τ x).head? = none›
      contradiction
  all_goals (simp only [eq_states] at eqs)

end Compiler
