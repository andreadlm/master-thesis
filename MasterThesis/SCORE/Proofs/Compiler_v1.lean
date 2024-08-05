import Mathlib.Tactic.Basic
import MasterThesis.SCORE.Interpreter
import MasterThesis.LOOP.Interpreter
import MasterThesis.SCORE.Compiler_v1

namespace SCORE

namespace l2s

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

/- Possibili formalizzazioni alternative con stato
  1) {σ : LOOP.Store} {τ τ' : SCORE.Store} (LP : LOOP.Com) : σ =ₛ τ → (SCORE.eval (l2s LP) (prog τ)) = (prog τ') → (LOOP.eval LP σ) =ₛ τ'
  2) {σ : LOOP.Store} {τ : SCORE.Store} (LP : LOOP.Com) : σ =ₛ τ → ∃ (τ' : SCORE.Store), (SCORE.eval (l2s LP) (prog τ) = (prog τ')) ∧ (LOOP.eval LP σ) =ₛ τ'

  Delle due, probabilmente la 2) è più forte, perchè dimostra che l'esecuzione di un programma compilato da LOOP non può mail fallire, ovvero il
  fallimento è una caratteristica dei soli programmi scritti direttamente in SCORE

  Oppure si introduce un tipo induttivo

  inductive LOOP.State : Type :=
  | prog : LOOP.Store → State

  che permette di estendere la definizione sopra

  def eq_states (s : LOOP.State) (t : SCORE.State) : Prop :=
    match s, t with
    | prog σ, prog τ => ∀ (x : Ident), (some (Int.ofNat (σ x)) = (τ x).head?)
    | _     , _      => False

  e mantenere sostazialmente invariate le definizioni dei teoremi.
  Gli altri lemmi seguono dalla scelta fatta per la soundness. -/

theorem soundness {σ : LOOP.Store} {τ : SCORE.Store} (LP : LOOP.Com) : σ =ₛ τ → (LOOP.eval LP σ) =ₛ (SCORE.eval (l2s LP) τ)
  intro
  induction LP generalizing σ τ with
  | SKIP =>
    rw [LOOP.eval, l2s, SCORE.eval]
    assumption
  | ZER x =>
    rw [LOOP.eval, l2s, SCORE.eval]
    intro y
    cases eq_or_ne x y with
    | inl /- x = y -/ =>
      have : ([x ↦ 0]σ) y = 0 := by
        { simp [‹x = y›] }; rw [this]
      have : ([x ↦ (0 :: τ x)]τ) y = (0 :: τ x) := by
        { simp [‹x = y›] }; rw [this]
      have : some (Int.ofNat 0) = some 0 := by
        { simp }; rw [this]
      rw [List.head?_cons]
    | inr /- x ≠ y -/ =>
      have : ([x ↦ 0]σ) y = σ y := by
        { simp [‹x ≠ y›] }; rw [this]
      have : ([x ↦ (0 :: τ x)]τ) y = τ y := by
        { simp [‹x ≠ y›] }; rw [this]
      exact ‹σ =ₛ τ› y
  | ASN x y =>
    rw [LOOP.eval, l2s]
    cases eq_or_ne x y with
    | inl /- x = y -/ =>
      have : (if x ≠ y then (CON x) ;; (FOR y (INC x)) else SKIP) = SKIP := by
        { simp [‹x = y›] }; rw [this]
      rw [SCORE.eval, ‹x = y›, LOOP.Store.update_no_update]
      assumption
    | inr /- x ≠ y -/ =>
      have : (if x ≠ y then (CON x) ;; (FOR y (INC x)) else SKIP) = (CON x) ;; (FOR y (INC x)) := by
        { simp [‹x ≠ y›] }; rw [this]
      repeat rw [SCORE.eval]
      have : ([x ↦ (0 :: τ x)]τ) y = τ y := by
        { simp [‹x ≠ y›] }; rw [this]; clear this
      simp only [← ‹σ =ₛ τ› y]
      induction (σ y) generalizing σ τ with
      | zero      =>
        have : (fun τ' ↦ eval (INC x) τ')^[0] ([x ↦ (0 :: τ x)]τ) = ([x ↦ (0 :: τ x)]τ) := by
          { simp }; rw [this]
        exact eq_stores_update x 0 ‹σ=ₛτ›
      | succ m ih =>
        have : (fun τ' ↦ eval (INC x) τ')^[m + 1] ([x ↦ (0 :: τ x)]τ) = eval (INC x) ((fun τ' ↦ eval (INC x) τ')^[m] ([x ↦ (0 :: τ x)]τ)) := by
          { simp [Nat.add_comm m 1, Function.iterate_add_apply] }; rw [this]
        exact eq_stores_INC (ih ‹σ =ₛ τ›)
  | INC x =>
    rw [LOOP.eval, l2s, SCORE.eval]
    intro y
    cases eq_or_ne x y with
    | inl /- x = y -/ =>
      have : ([x ↦ (σ x + 1)]σ) y = σ y + 1 := by
        { simp [‹x = y›] }; rw [this]
      simp only [‹x = y›, ← ‹σ =ₛ τ› y]
      have : ([y ↦ ((Int.ofNat (σ y) + 1) :: (τ y).tail)]τ) y = ((Int.ofNat (σ y) + 1) :: (τ y).tail) := by
        { simp }; rw [this]
      rw [List.head?_cons]
      have : some (Int.ofNat (σ y + 1)) = some (Int.ofNat (σ y) + 1) := by
        { simp }; rw [this]
    | inr /- x ≠ y -/ =>
      have : ([x ↦ (σ x + 1)]σ) y = σ y := by
        { simp [‹x ≠ y›] }; rw [this]
      simp only [‹x ≠ y›, ← ‹σ =ₛ τ› x]
      have : ([x ↦ ((Int.ofNat (σ x) + 1) :: (τ x).tail)]τ) y = τ y := by
        { simp [‹x ≠ y›] }; rw [this]
      exact ‹σ =ₛ τ› y
  | SEQ LQ LR ih₁ ih₂ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    exact ih₂ (ih₁ ‹σ =ₛ τ›)
  | FOR x LQ ih₁ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    simp only [← ‹σ =ₛ τ› x]
    induction (σ x) generalizing σ τ with
    | zero       =>
      have : (fun σ' ↦ LOOP.eval LQ σ')^[0] σ = σ := by
        { simp }; rw [this];
      have : (fun τ' ↦ eval (l2s LQ) τ')^[0] τ = τ := by
        { simp }; rw [this];
      assumption
    | succ _ ih₂ => exact ih₂ (ih₁ ‹σ =ₛ τ›)

end l2s

end SCORE
