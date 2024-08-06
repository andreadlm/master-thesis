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
        have : (([x ↦ 0 :: σ x] σ) x).head? = some 0 := by
          calc
            (([x ↦ 0 :: σ x] σ) x).head?
            _ = (0 :: σ x).head? := by simp
            _ = some 0           := by simp
        simp only [this]
        calc
          prog ([x ↦ (([x ↦ 0 :: σ x] σ) x).tail][x ↦ 0 :: σ x] σ)
          _ = prog ([x ↦ (([x ↦ 0 :: σ x] σ) x).tail] σ) := by rw [update_shrink]
          _ = prog ([x ↦ (0 :: σ x).tail] σ)             := by simp
          _ = prog ([x ↦ σ x] σ)                         := by simp
          _ = prog σ                                     := by rw [update_unchanged]
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
          have : ([x ↦ (σ x).tail] σ) x = (σ x).tail := by simp
          rw [this, update_shrink, update_unchanged_cons ‹(σ x).head? = some 0›]
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
          have : (([x ↦ (v - 1) :: (σ x).tail] σ) x).head? = some (v - 1) := by
            calc
              (([x ↦ ((v - 1) :: (σ x).tail)] σ) x).head?
              _ = ((v - 1) :: (σ x).tail).head? := by simp
              _ = some (v - 1)                  := by simp
          simp only [this, update_shrink]
          calc
            prog ([x ↦ (v - 1 + 1) :: (([x ↦ (v - 1) :: (σ x).tail] σ) x).tail] σ)
            _ = prog ([x ↦ v :: (([x ↦ (v - 1) :: (σ x).tail] σ) x).tail] σ) := by rw [Int.sub_add_cancel]
            _ = prog ([x ↦ v :: ((v - 1) :: (σ x).tail).tail] σ)              := by simp
            _ = prog ([x ↦ v :: (σ x).tail] σ)                               := by simp
            _ = prog σ                                                       := by rw [update_unchanged_cons ‹(σ x).head? = some v›]
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
