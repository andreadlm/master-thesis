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
      constructor
      case left  =>
        rw [eval] at ‹eval SKIP (prog σ) = q›
        rw [← ‹prog σ = q›, inv, eval]
      case right =>
        by_contra
        simp only [‹prog σ = ⊥›, eval] at ‹eval SKIP (prog σ) = q›
        symm at ‹⊥ = q›
        contradiction
    | ⊥      =>
      rw [eval] at ‹eval SKIP ⊥ = q›
      symm at ‹⊥ = q›
      contradiction
  case mpr =>
    intro
    have ⟨_, _⟩ := ‹eval SKIP⁻¹ q = p ∧ p ≠ ⊥›
    match q with
      | prog σ =>
        constructor
        case left  =>
          rw [inv, eval] at ‹eval SKIP⁻¹ (prog σ) = p›
          rw [← ‹prog σ = p›, eval]
        case right =>
          by_contra
          simp only [‹prog σ = ⊥›, eval] at ‹eval SKIP (prog σ) = p›
          symm at ‹⊥ = p›
          contradiction
      | ⊥      =>
        rw [inv, eval] at ‹eval SKIP⁻¹ ⊥ = p›
        symm at ‹⊥ = p›
        contradiction

lemma CON_inv_CON {p q : state} {x : ident} : (eval (CON x) p) = q ∧ q ≠ ⊥ ↔ (eval (CON x)⁻¹ q) = p ∧ p ≠ ⊥ := by
  constructor
  case mp  =>
    intro
    have ⟨_, _⟩ := ‹eval (CON x) p = q ∧ q ≠ ⊥›
    clear ‹eval (CON x) p = q ∧ q ≠ ⊥›
    match p with
    | prog σ =>
      constructor
      case left  =>
        rw [eval] at ‹eval (CON x) (prog σ) = q›
        rw [← ‹prog ([x ↦ (0 :: σ x)] σ) = q›, inv, eval]
        have : ([x ↦ (0 :: σ x)] σ) x = (0 :: σ x) := by
          { simp }; rw [this]
        have : (0 :: σ x).head? = some 0 := by
          { simp }; simp only [this]
        have : (0 :: σ x).tail = σ x := by
          { simp }; rw [this]
        rw [update_shrink, update_unchanged]
      case right =>
        by_contra
        simp only [‹prog σ = ⊥›, eval] at ‹eval (CON x) (prog σ) = q›
        symm at ‹⊥ = q›
        contradiction
    | ⊥      =>
      rw [eval] at ‹eval (CON x) ⊥ = q›
      symm at ‹⊥ = q›
      contradiction
  case mpr =>
    intro
    have ⟨lh, _⟩ := ‹eval (CON x)⁻¹ q = p ∧ p ≠ ⊥›
    clear ‹eval (CON x)⁻¹ q = p ∧ p ≠ ⊥›
    match q with
    | prog σ =>
      constructor
      case left  =>
        rw [inv, eval] at ‹eval (CON x)⁻¹ (prog σ) = p›
        split at lh
        case h_1 =>
          rw [← ‹prog ([x ↦ (σ x).tail]σ) = p›, eval]
          have : ([x ↦ (σ x).tail] σ) x = (σ x).tail := by
            { simp }; rw [this]
          rw [update_shrink]
          rw [update_unchanged_cons ‹(σ x).head? = some 0›]
        case h_2 =>
          symm at ‹⊥ = p›
          contradiction
      case right =>
        by_contra
        simp only [‹prog σ = ⊥›, eval] at ‹eval (CON x)⁻¹ (prog σ) = p›
        symm at ‹⊥ = p›
        contradiction
    | ⊥      =>
      rw [inv, eval] at ‹eval (CON x)⁻¹ ⊥ = p›
      symm at ‹⊥ = p›
      contradiction
