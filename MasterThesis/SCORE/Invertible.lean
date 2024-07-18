import MasterThesis.Commons
import MasterThesis.SCORE.Language
import MasterThesis.SCORE.Interpreter

open SCORE SCORE.com SCORE.store SCORE.state

lemma invertible_SKIP {s t : state} : (eval SKIP s) = t ∧ t ≠ ⊥ ↔ (eval SKIP⁻¹ t) = s ∧ s ≠ ⊥ := by
  constructor
  case mp  =>
    intro
    have ⟨_, _⟩ := ‹eval SKIP s = t ∧ t ≠ ⊥›
    match s with
    | prog σ =>
      constructor
      case left  =>
        rw [eval] at ‹eval SKIP (prog σ) = t›
        rw [← ‹prog σ = t›, inv, eval]
      case right =>
        by_contra
        simp only [‹prog σ = ⊥›, eval] at ‹eval SKIP (prog σ) = t›
        symm at ‹⊥ = t›
        contradiction
    | ⊥      =>
      rw [eval] at ‹eval SKIP ⊥ = t›
      symm at ‹⊥ = t›
      contradiction
  case mpr =>
    intro
    have ⟨_, _⟩ := ‹eval SKIP⁻¹ t = s ∧ s ≠ ⊥›
    match t with
      | prog σ =>
        constructor
        case left  =>
          rw [inv, eval] at ‹eval SKIP⁻¹ (prog σ) = s›
          rw [← ‹prog σ = s›, eval]
        case right =>
          by_contra
          simp only [‹prog σ = ⊥›, eval] at ‹eval SKIP (prog σ) = s›
          symm at ‹⊥ = s›
          contradiction
      | ⊥      =>
        rw [inv, eval] at ‹eval SKIP⁻¹ ⊥ = s›
        symm at ‹⊥ = s›
        contradiction

lemma invertible_CON {s t : state} {x : ident} : (eval (CON x) s) = t ∧ t ≠ ⊥ ↔ (eval (CON x)⁻¹ t) = s ∧ s ≠ ⊥ := by
  constructor
  case mp  =>
    intro
    have ⟨_, _⟩ := ‹eval (CON x) s = t ∧ t ≠ ⊥›
    clear ‹eval (CON x) s = t ∧ t ≠ ⊥›
    match s with
    | prog σ =>
      constructor
      case left  =>
        rw [eval] at ‹eval (CON x) (prog σ) = t›
        rw [← ‹prog ([x ↦ (0 :: σ x)] σ) = t›, inv, eval]
        have : ([x ↦ (0 :: σ x)] σ) x = (0 :: σ x) := by
          { simp }; rw [this]
        have : (0 :: σ x).head? = some 0 := by
          { simp }; simp only [this]
        have : (0 :: σ x).tail = σ x := by
          { simp }; rw [this]
        rw [update_shrink, update_unchanged]
      case right =>
        by_contra
        simp only [‹prog σ = ⊥›, eval] at ‹eval (CON x) (prog σ) = t›
        symm at ‹⊥ = t›
        contradiction
    | ⊥      =>
      rw [eval] at ‹eval (CON x) ⊥ = t›
      symm at ‹⊥ = t›
      contradiction
  case mpr =>
    intro
    have ⟨lh, _⟩ := ‹eval (CON x)⁻¹ t = s ∧ s ≠ ⊥›
    clear ‹eval (CON x)⁻¹ t = s ∧ s ≠ ⊥›
    match t with
    | prog σ =>
      constructor
      case left  =>
        rw [inv, eval] at ‹eval (CON x)⁻¹ (prog σ) = s›
        split at lh
        case h_1 =>
          rw [← ‹prog ([x ↦ (σ x).tail]σ) = s›, eval]
          have : ([x ↦ (σ x).tail] σ) x = (σ x).tail := by
            { simp }; rw [this]
          rw [update_shrink]
          rw [update_unchanged_cons ‹(σ x).head? = some 0›]
        case h_2 =>
          symm at ‹⊥ = s›
          contradiction
      case right =>
        by_contra
        simp only [‹prog σ = ⊥›, eval] at ‹eval (CON x)⁻¹ (prog σ) = s›
        symm at ‹⊥ = s›
        contradiction
    | ⊥      =>
      rw [inv, eval] at ‹eval (CON x)⁻¹ ⊥ = s›
      symm at ‹⊥ = s›
      contradiction

lemma invertible_NOC {s t : state} {x : ident} : (eval (NOC x) s) = t ∧ t ≠ ⊥ ↔ (eval (NOC x)⁻¹ t) = s ∧ s ≠ ⊥ := by
  have : (NOC x) = (CON x)⁻¹ := by
    { rw [inv] }; rw [this]
  rw [inv]
  exact invertible_CON.symm

lemma invertible_DEC {s t : state} {x : ident} : (eval (DEC x) s) = t ∧ t ≠ ⊥ ↔ (eval (DEC x)⁻¹ t) = s ∧ s ≠ ⊥ := by
  constructor
  case mp  =>
    intro
    have ⟨lh, _⟩ := ‹eval (DEC x) s = t ∧ t ≠ ⊥›
    clear ‹eval (DEC x) s = t ∧ t ≠ ⊥›
    match s with
    | prog σ =>
      constructor
      case left =>
        rw [eval] at ‹eval (DEC x) (prog σ) = t›
        split at lh
        case h_1 v _ =>
          rw [← ‹prog ([x ↦ ((v - 1) :: (σ x).tail)]σ) = t›, inv, eval]
          have : ([x ↦ ((v - 1) :: (σ x).tail)] σ) x = (v - 1) :: (σ x).tail := by
            { simp }; rw [this]
          have : ((v - 1) :: (σ x).tail).head? = some (v - 1) := by
            { rw [List.head?] }; simp only [this]
          rw [update_shrink]
          have : (v - 1 + 1) = v := by
            { rw [Int.sub_add_cancel] }; rw [this]
          have : ((v - 1) :: (σ x).tail).tail = (σ x).tail := by
            { rw [List.tail_cons] }; rw [this]
          rw [update_unchanged_cons ‹(σ x).head? = some v›]
        case h_2 =>
          symm at ‹⊥ = t›
          contradiction
      case right =>
        by_contra
        simp only [‹prog σ = ⊥›, eval] at ‹eval (DEC x) (prog σ) = t›
        symm at ‹⊥ = t›
        contradiction
    | ⊥      =>
      rw [eval] at ‹eval (DEC x) ⊥ = t›
      symm at ‹⊥ = t›
      contradiction
  case mpr =>
    intro
    have ⟨lh, _⟩ := ‹eval (DEC x)⁻¹ t = s ∧ s ≠ ⊥›
    clear ‹eval (DEC x)⁻¹ t = s ∧ s ≠ ⊥›
    match t with
    | prog σ =>
      constructor
      case left =>
        rw [inv, eval] at ‹eval (DEC x)⁻¹ (prog σ) = s›
        split at lh
        case h_1 v _ =>
          rw [← ‹prog ([x ↦ ((v + 1) :: (σ x).tail)]σ) = s›, eval]
          have : ([x ↦ ((v + 1) :: (σ x).tail)] σ) x = (v + 1) :: (σ x).tail := by
            { simp }; rw [this]
          have : ((v + 1) :: (σ x).tail).head? = some (v + 1) := by
            { rw [List.head?] }; simp only [this]
          rw [update_shrink]
          have : (v + 1 - 1) = v := by
            { rw [Int.add_sub_cancel] }; rw [this]
          have : ((v + 1) :: (σ x).tail).tail = (σ x).tail := by
            { rw [List.tail_cons] }; rw [this]
          rw [update_unchanged_cons ‹(σ x).head? = some v›]
        case h_2 =>
          symm at ‹⊥ = s›
          contradiction
      case right =>
        by_contra
        simp only [‹prog σ = ⊥›, inv, eval] at ‹eval (DEC x)⁻¹ (prog σ) = s›
        symm at ‹⊥ = s›
        contradiction
    | ⊥ =>
      rw [inv, eval] at ‹eval (DEC x)⁻¹ ⊥ = s›
      symm at ‹⊥ = s›
      contradiction

lemma invertible_INC {s t : state} {x : ident} : (eval (INC x) s) = t ∧ t ≠ ⊥ ↔ (eval (INC x)⁻¹ t) = s ∧ s ≠ ⊥ := by
  have : (INC x) = (DEC x)⁻¹ := by
    { rw [inv] }; rw [this]
  rw [inv]
  exact invertible_DEC.symm

lemma invertible_SEQ {s t : state} {P Q : com} (ih₁ : ∀ {s t : state}, eval P s = t ∧ t ≠ ⊥ ↔ eval P⁻¹ t = s ∧ s ≠ ⊥) (ih₂ : ∀ {s t : state}, eval Q s = t ∧ t ≠ ⊥ ↔ eval Q⁻¹ t = s ∧ s ≠ ⊥) : (eval (SEQ P Q) s) = t ∧ t ≠ ⊥ ↔ (eval (SEQ P Q)⁻¹ t) = s ∧ s ≠ ⊥ := by
  constructor
  case mp =>
    intro
    have ⟨_, _⟩ := ‹eval (P ;; Q) s = t ∧ t ≠ ⊥›
    clear ‹eval (P ;; Q) s = t ∧ t ≠ ⊥›
    match s, t with
    | prog σ, prog τ =>
      rw [inv, eval]
      rw [eval] at ‹eval (P ;; Q) (prog σ) = prog τ›
      have ⟨_, _⟩ := ih₂.mp ⟨‹eval Q (eval P (prog σ)) = prog τ›, ‹prog τ ≠ ⊥›⟩
      have : eval Q⁻¹ (prog τ) ≠ ⊥ := Eq.trans_ne ‹eval Q⁻¹ (prog τ) = eval P (prog σ)› ‹eval P (prog σ) ≠ ⊥›
      exact ih₁.mp ⟨‹eval Q⁻¹ (prog τ) = eval P (prog σ)›.symm, ‹eval Q⁻¹ (prog τ) ≠ ⊥›⟩
    | _, _           => sorry
  case mpr =>
    sorry

theorem invertible {s t : state} {P : com} : (eval P s) = t ∧ t ≠ ⊥ ↔ (eval P⁻¹ t) = s ∧ s ≠ ⊥ := by
  induction P generalizing s t
  case SKIP => sorry
  case CON => sorry
  case NOC => sorry
  case DEC => sorry
  case INC => sorry
  case SEQ P Q ih₁ ih₂ => sorry
  case FOR x P => sorry
