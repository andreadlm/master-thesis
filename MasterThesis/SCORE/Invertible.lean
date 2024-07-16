import MasterThesis.Commons
import MasterThesis.SCORE.Language
import MasterThesis.SCORE.Interpreter

open SCORE SCORE.com SCORE.store SCORE.state

lemma SKIP_inv_SKIP {p q : state} : (eval SKIP p) = q ∧ q ≠ ⊥ ↔ (eval SKIP⁻¹ q) = p ∧ p ≠ ⊥ := by
  constructor
  case mp  =>
    intro
    have ⟨_, _⟩ := ‹eval SKIP p = q ∧ q ≠ ⊥›
    match p with
    | prog σ =>
      rw [eval] at ‹eval SKIP (prog σ) = q›
      constructor
      case left  => rw [← ‹prog σ = q›, inv, eval]
      case right => rwa [‹prog σ = q›]
    | ⊥      =>
      rw [eval] at ‹eval SKIP ⊥ = q›
      symm at ‹⊥ = q›
      contradiction
  case mpr =>
    intro
    have ⟨_, _⟩ := ‹eval SKIP⁻¹ q = p ∧ p ≠ ⊥›
    match q with
      | prog σ =>
        rw [inv, eval] at ‹eval SKIP⁻¹ (prog σ) = p›
        constructor
        case left  => rw [← ‹prog σ = p›, eval]
        case right => rwa [‹prog σ = p›]
      | ⊥      =>
        rw [inv, eval] at ‹eval SKIP⁻¹ ⊥ = p›
        symm at ‹⊥ = p›
        contradiction
