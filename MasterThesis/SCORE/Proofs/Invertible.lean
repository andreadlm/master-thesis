import MasterThesis.SCORE.Proofs.Language
import MasterThesis.SCORE.Interpreter

open SCORE Com Store State

lemma invertible_SKIP {s t : State} : (eval SKIP s) = t ∧ t ≠ ⊥ ↔ (eval SKIP⁻¹ t) = s ∧ s ≠ ⊥ := by
  constructor
  case mp  =>
    intro
    have ⟨_, _⟩ := ‹eval SKIP s = t ∧ t ≠ ⊥›
    match s with
    | some σ =>
      constructor
      case left  =>
        rw [eval] at ‹eval SKIP (some σ) = t›
        rw [inv, ←‹some σ = t›, eval]
      case right =>
        by_contra
        simp only [‹some σ = ⊥›, eval] at ‹eval SKIP (some σ) = t›
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
      | some σ =>
        constructor
        case left  =>
          rw [inv, eval] at ‹eval SKIP⁻¹ (some σ) = s›
          rw [←‹some σ = s›, eval]
        case right =>
          by_contra
          simp only [‹some σ = ⊥›, eval] at ‹eval SKIP (some σ) = s›
          symm at ‹⊥ = s›
          contradiction
      | ⊥      =>
        rw [inv, eval] at ‹eval SKIP⁻¹ ⊥ = s›
        symm at ‹⊥ = s›
        contradiction

lemma invertible_CON {s t : State} {x : Ident} : (eval (CON x) s) = t ∧ t ≠ ⊥ ↔ (eval (CON x)⁻¹ t) = s ∧ s ≠ ⊥ := by
  constructor
  case mp  =>
    intro
    have ⟨_, _⟩ := ‹eval (CON x) s = t ∧ t ≠ ⊥›
    clear ‹eval (CON x) s = t ∧ t ≠ ⊥›
    match s with
    | some σ =>
      constructor
      case left  =>
        rw [eval] at ‹eval (CON x) (some σ) = t›
        rw [←‹some (σ[x ↦ 0 :: σ x]) = t›, inv, eval]
        simp
      case right =>
        by_contra
        simp only [‹some σ = ⊥›, eval] at ‹eval (CON x) (some σ) = t›
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
    | some σ =>
      constructor
      case left  =>
        rw [inv, eval] at ‹eval (CON x)⁻¹ (some σ) = s›
        split at lh
        case h_1 =>
          rw [←‹some (σ[x ↦ (σ x).tail]) = s›, eval]
          simp [update_unchanged_cons ‹(σ x).head? = some 0›]
        case h_2 =>
          symm at ‹⊥ = s›
          contradiction
      case right =>
        by_contra
        simp only [‹some σ = ⊥›, eval] at ‹eval (CON x)⁻¹ (some σ) = s›
        symm at ‹⊥ = s›
        contradiction
    | ⊥      =>
      rw [inv, eval] at ‹eval (CON x)⁻¹ ⊥ = s›
      symm at ‹⊥ = s›
      contradiction

lemma invertible_NOC {s t : State} {x : Ident} : (eval (NOC x) s) = t ∧ t ≠ ⊥ ↔ (eval (NOC x)⁻¹ t) = s ∧ s ≠ ⊥ := by
  have : (NOC x) = (CON x)⁻¹ := by rw [inv]
  rw [this, inv]
  exact invertible_CON.symm

lemma invertible_DEC {s t : State} {x : Ident} : (eval (DEC x) s) = t ∧ t ≠ ⊥ ↔ (eval (DEC x)⁻¹ t) = s ∧ s ≠ ⊥ := by
  constructor
  case mp  =>
    intro
    have ⟨lh, _⟩ := ‹eval (DEC x) s = t ∧ t ≠ ⊥›
    clear ‹eval (DEC x) s = t ∧ t ≠ ⊥›
    match s with
    | some σ =>
      constructor
      case left =>
        rw [eval] at ‹eval (DEC x) (some σ) = t›
        split at lh
        case h_1 v _ =>
          rw [inv, ←‹some (σ[x ↦ (v - 1) :: (σ x).tail]) = t›, eval]
          simp [update_unchanged_cons ‹(σ x).head? = some v›]
        case h_2 =>
          symm at ‹⊥ = t›
          contradiction
      case right =>
        by_contra
        simp only [‹some σ = ⊥›, eval] at ‹eval (DEC x) (some σ) = t›
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
    | some σ =>
      constructor
      case left =>
        rw [inv, eval] at ‹eval (DEC x)⁻¹ (some σ) = s›
        split at lh
        case h_1 v _ =>
          rw [←‹some (σ[x ↦ ((v + 1) :: (σ x).tail)]) = s›, eval]
          simp [update_unchanged_cons ‹(σ x).head? = some v›]
        case h_2 =>
          symm at ‹⊥ = s›
          contradiction
      case right =>
        by_contra
        simp only [‹some σ = ⊥›, inv, eval] at ‹eval (DEC x)⁻¹ (some σ) = s›
        symm at ‹⊥ = s›
        contradiction
    | ⊥ =>
      rw [inv, eval] at ‹eval (DEC x)⁻¹ ⊥ = s›
      symm at ‹⊥ = s›
      contradiction

lemma invertible_INC {s t : State} {x : Ident} : (eval (INC x) s) = t ∧ t ≠ ⊥ ↔ (eval (INC x)⁻¹ t) = s ∧ s ≠ ⊥ := by
  have : (INC x) = (DEC x)⁻¹ := by
    { rw [inv] }; rw [this]
  rw [inv]
  exact invertible_DEC.symm

lemma invertible_SEQ {s t : State} {P Q : Com} (ih₁ : ∀ {s t : State}, eval P s = t ∧ t ≠ ⊥ ↔ eval P⁻¹ t = s ∧ s ≠ ⊥) (ih₂ : ∀ {s t : State}, eval Q s = t ∧ t ≠ ⊥ ↔ eval Q⁻¹ t = s ∧ s ≠ ⊥) : (eval (SEQ P Q) s) = t ∧ t ≠ ⊥ ↔ (eval (SEQ P Q)⁻¹ t) = s ∧ s ≠ ⊥ := by
  constructor
  case mp =>
    intro
    have ⟨_, _⟩ := ‹eval (P ;; Q) s = t ∧ t ≠ ⊥›
    clear ‹eval (P ;; Q) s = t ∧ t ≠ ⊥›
    match s, t with
    | some σ, some τ =>
      rw [inv, eval]
      rw [eval] at ‹eval (P ;; Q) (some σ) = some τ›
      have ⟨_, _⟩ := ih₂.mp ⟨‹eval Q (eval P (some σ)) = some τ›, ‹some τ ≠ ⊥›⟩
      have : eval Q⁻¹ (some τ) ≠ ⊥ := Eq.trans_ne ‹eval Q⁻¹ (some τ) = eval P (some σ)› ‹eval P (some σ) ≠ ⊥›
      exact ih₁.mp ⟨‹eval Q⁻¹ (some τ) = eval P (some σ)›.symm, ‹eval Q⁻¹ (some τ) ≠ ⊥›⟩
    | ⊥     , t      =>
      rw [eval] at ‹eval (P ;; Q) ⊥ = t›
      symm at ‹⊥ = t›
      contradiction
    | s     , ⊥     =>
      contradiction
  case mpr =>
    intro
    have ⟨_, _⟩ := ‹eval (P ;; Q)⁻¹ t = s ∧ s ≠ ⊥›
    clear ‹eval (P ;; Q)⁻¹ t = s ∧ s ≠ ⊥›
    match t, s with
    | some τ, some σ =>
      rw [eval]
      rw [inv, eval] at ‹eval (P ;; Q)⁻¹ (some τ) = some σ›
      have ⟨_, _⟩ := ih₁.mpr ⟨‹eval P⁻¹ (eval Q⁻¹ (some τ)) = some σ›, ‹some σ ≠ ⊥›⟩
      have : eval P (some σ) ≠ ⊥ := Eq.trans_ne ‹eval P (some σ) = eval Q⁻¹ (some τ)› ‹eval Q⁻¹ (some τ) ≠ ⊥›
      exact ih₂.mpr ⟨‹eval P (some σ) = eval Q⁻¹ (some τ)›.symm, ‹eval P (some σ) ≠ ⊥›⟩
    | t     , ⊥      =>
      contradiction
    | ⊥     , s      =>
      rw [inv, eval] at ‹eval (P ;; Q)⁻¹ ⊥ = s›
      symm at ‹⊥ = s›
      contradiction

theorem invertible {s t : State} {P : Com} : (eval P s) = t ∧ t ≠ ⊥ ↔ (eval P⁻¹ t) = s ∧ s ≠ ⊥ := by
  induction P generalizing s t
  case SKIP        => exact invertible_SKIP
  case CON         => exact invertible_CON
  case NOC         => exact invertible_NOC
  case DEC         => exact invertible_DEC
  case INC         => exact invertible_INC
  case SEQ ih₁ ih₂ => exact invertible_SEQ ih₁ ih₂
  case FOR x P     => sorry
