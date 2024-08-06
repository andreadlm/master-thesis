import MasterThesis.SCORE.Proofs.Language
import MasterThesis.SCORE.Interpreter

open SCORE Com Store State

lemma invertible_SKIP {s t : State} : (eval SKIP s) = t ∧ t ≠ ⊥ ↔ (eval SKIP⁻¹ t) = s ∧ s ≠ ⊥ := by
  constructor
  case mp  =>
    intro
    have ⟨_, _⟩ := ‹eval SKIP s = t ∧ t ≠ ⊥›
    match s with
    | prog σ =>
      constructor
      case left  =>
        rw [eval] at ‹eval SKIP (prog σ) = t›
        rw [inv, ←‹prog σ = t›, eval]
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
          rw [←‹prog σ = s›, eval]
        case right =>
          by_contra
          simp only [‹prog σ = ⊥›, eval] at ‹eval SKIP (prog σ) = s›
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
    | prog σ =>
      constructor
      case left  =>
        rw [eval] at ‹eval (CON x) (prog σ) = t›
        rw [←‹prog ([x ↦ 0 :: σ x] σ) = t›, inv, eval]
        simp
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
          rw [←‹prog ([x ↦ (σ x).tail] σ) = s›, eval]
          simp [update_unchanged_cons ‹(σ x).head? = some 0›]
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
    | prog σ =>
      constructor
      case left =>
        rw [eval] at ‹eval (DEC x) (prog σ) = t›
        split at lh
        case h_1 v _ =>
          rw [inv, ←‹prog ([x ↦ (v - 1) :: (σ x).tail] σ) = t›, eval]
          simp [update_unchanged_cons ‹(σ x).head? = some v›]
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
          rw [←‹prog ([x ↦ ((v + 1) :: (σ x).tail)]σ) = s›, eval]
          simp [update_unchanged_cons ‹(σ x).head? = some v›]
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
    | prog σ, prog τ =>
      rw [inv, eval]
      rw [eval] at ‹eval (P ;; Q) (prog σ) = prog τ›
      have ⟨_, _⟩ := ih₂.mp ⟨‹eval Q (eval P (prog σ)) = prog τ›, ‹prog τ ≠ ⊥›⟩
      have : eval Q⁻¹ (prog τ) ≠ ⊥ := Eq.trans_ne ‹eval Q⁻¹ (prog τ) = eval P (prog σ)› ‹eval P (prog σ) ≠ ⊥›
      exact ih₁.mp ⟨‹eval Q⁻¹ (prog τ) = eval P (prog σ)›.symm, ‹eval Q⁻¹ (prog τ) ≠ ⊥›⟩
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
    | prog τ, prog σ =>
      rw [eval]
      rw [inv, eval] at ‹eval (P ;; Q)⁻¹ (prog τ) = prog σ›
      have ⟨_, _⟩ := ih₁.mpr ⟨‹eval P⁻¹ (eval Q⁻¹ (prog τ)) = prog σ›, ‹prog σ ≠ ⊥›⟩
      have : eval P (prog σ) ≠ ⊥ := Eq.trans_ne ‹eval P (prog σ) = eval Q⁻¹ (prog τ)› ‹eval Q⁻¹ (prog τ) ≠ ⊥›
      exact ih₂.mpr ⟨‹eval P (prog σ) = eval Q⁻¹ (prog τ)›.symm, ‹eval P (prog σ) ≠ ⊥›⟩
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

/- Definizione di invertible data per il linguaggio SCORE privo di stati di errore.
  La condizione è dimostrabile per mezzo di invertible nel caso in cui non si verifichino errori,
  nel caso di situazioni di errore però non risulta essere adatta. I sorry da dimostrare sono "banali".
-/
theorem invertible' {s : State} {P : Com} : (eval (P ;; P⁻¹) s) = s := by
  have : (eval (P ;; P⁻¹) s) = eval P⁻¹ (eval P s) := by
    { sorry }; rw [this]
  have := prog_or_bot (eval P s)
  cases ‹(∃ σ, eval P s = prog σ) ∨ eval P s = ⊥›
  case inl =>
    have ⟨σ, _⟩ := ‹∃ σ, eval P s = prog σ›
    have : prog σ ≠ ⊥ := by sorry
    have := (invertible.mp ⟨‹eval P s = prog σ›, ‹prog σ ≠ ⊥›⟩).left
    rw [←‹eval P s = prog σ›] at ‹eval P⁻¹ (prog σ) = s›
    assumption
  case inr =>
    match s with
    | prog σ =>
      rw [‹eval P (prog σ) = ⊥›, eval]
      sorry -- Impossibile che ⊥ = prog σ
    | ⊥      =>
      rw [eval]
      have : eval P⁻¹ ⊥ = ⊥ := by
        { sorry }; rw [this]
