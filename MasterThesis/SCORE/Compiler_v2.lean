import MasterThesis.SCORE.Language
import MasterThesis.SCORE.Interpreter
import MasterThesis.LOOP.Language
import MasterThesis.LOOP.Interpreter
import Mathlib.Tactic.Linarith

namespace SCORE

open SCORE.com

def L2S' (ev : ident) (Lc: LOOP.com) : SCORE.com :=
  match Lc with
  | LOOP.com.SKIP    => SKIP
  | LOOP.com.ZER x   => CON x
  | LOOP.com.ASN x y => FOR y (INC ev) ;;
                        CON x ;;
                        FOR ev (INC x) ;;
                        FOR x (DEC ev)
  | LOOP.com.INC x   => INC x
  | LOOP.com.SEQ P Q => L2S' ev P ;;
                        L2S' ev Q
  | LOOP.com.FOR x P => FOR x (L2S' ev P)

namespace L2S'

example : - Int.negSucc u = Int.ofNat u.succ := by simp [Int.negSucc_coe]

-- TODO: sostituire con un teorema più generale sulla reversibilità?
lemma eval_inc_dec_evalI {x : ident} {σ : SCORE.store} : eval (INC x) σ = evalI (DEC x) σ := by
  rw [SCORE.eval, SCORE.evalI]

-- TODO: sostituire con un teorema più generale sulla reversibilità?
lemma eval_dec_inc_evalI {x : ident} {σ : SCORE.store} : eval (DEC x) σ = evalI (INC x) σ := by
  rw [SCORE.eval, SCORE.evalI]

lemma iter_inc {x : ident} {σ : SCORE.store} {k : Int} (v : ℕ) : (σ x).head! = k → (fun τ ↦ eval (INC x) τ)^[v] σ = [x ↦ ((k + Int.ofNat v) :: (σ x).tail!)]σ := by
  intros
  induction v generalizing σ with
  | zero      =>
    have : (fun τ ↦ eval (INC x) τ)^[0] σ = σ := by
      { simp }; rw [this]
    have : (k + Int.ofNat 0) = k := by
      { simp }; rw [this]
    exact SCORE.store.update_unchanged_cons ‹(σ x).head! = k›
  | succ m ih =>
    have : (fun τ ↦ eval (INC x) τ)^[m + 1] σ = eval (INC x) ((fun τ ↦ eval (INC x) τ)^[m] σ) := by
      { simp [Nat.add_comm m 1, Function.iterate_add_apply] }; rw[this]
    rw [ih ‹(σ x).head! = k›, SCORE.eval, SCORE.store.update_shrink]
    have : (([x ↦ ((k + Int.ofNat m) :: (σ x).tail!)]σ) x).head! = (k + Int.ofNat m) := by
      { simp [List.head!] }; rw [this]
    have : (([x ↦ ((k + Int.ofNat m) :: (σ x).tail!)]σ) x).tail! = (σ x).tail! := by
      { simp }; rw [this]
    funext y
    cases eq_or_ne x y with
    | inl =>
      rw [← ‹x = y›]
      have : ([x ↦ ((k + Int.ofNat m + 1) :: (σ x).tail!)]σ) x = ((k + Int.ofNat m + 1) :: (σ x).tail!) := by
        { simp }; rw [this]
      have : ([x ↦ ((k + Int.ofNat (m + 1)) :: (σ x).tail!)]σ) x = ((k + (Int.ofNat m + 1)) :: (σ x).tail!) := by
        { simp }; rw [this]
      have : (k + Int.ofNat m + 1) = (k + (Int.ofNat m + 1)) := by
        { linarith }; rw [this]
    | inr =>
      have : ([x ↦ ((k + Int.ofNat m + 1) :: (σ x).tail!)]σ) y = σ y := by
        { simp [‹x ≠ y›] }; rw [this]
      have : ([x ↦ ((k + Int.ofNat (m + 1)) :: (σ x).tail!)]σ) y = σ y := by
        { simp [‹x ≠ y›] }; rw [this]

lemma iter_dec {x : ident} {σ: SCORE.store} {k : Int} (v : ℕ) : (σ x).head! = k → (fun τ ↦ eval (DEC x) τ)^[v] σ = [x ↦ ((k - Int.ofNat v) :: (σ x).tail!)]σ := sorry

lemma for_inc {x y : ident} {v₁ v₂ : Int} {τ : SCORE.store} : (τ x).head! = v₁ → (τ y).head! = v₂ → eval (FOR y (INC x)) τ = [x ↦ ((v₁ + v₂) :: (τ x).tail!)]τ := by
  intros
  rw [SCORE.eval]
  split
  case h_1 v _ /- (τ y).head! >= 0 -/ =>
    have : v₂ = Int.ofNat v := by
      { rw [← ‹(τ y).head! = v₂›, ‹(τ y).head! = Int.ofNat v›] }; rw [this]
    exact iter_inc v ‹(τ x).head! = v₁›
  case h_2 u _ /- (τ y).head! < 0 -/  =>
    simp only [← eval_dec_inc_evalI]
    have : v₂ = Int.negSucc u := by
      { rw [← ‹(τ y).head! = v₂›, ‹(τ y).head! = Int.negSucc u›] }; rw [this]
    have : v₁ + Int.negSucc u = v₁ - Int.ofNat (u.succ) := by
      { simp [Int.negSucc_coe]; linarith }; rw [this]
    exact iter_dec u.succ ‹(τ x).head! = v₁›

lemma for_dec {x y : ident} {v₁ v₂ : Int} {τ : SCORE.store} : (τ x).head! = v₁ → (τ y).head! = v₂ → eval (FOR y (DEC x)) τ = [x ↦ ((v₁ - v₂) :: (τ x).tail!)]τ := by
  intros
  rw [SCORE.eval]
  split
  case h_1 v _ /- (τ y).head! >= 0 -/ =>
    have : v₂ = Int.ofNat v := by
      { rw [← ‹(τ y).head! = v₂›, ‹(τ y).head! = Int.ofNat v›] }; rw [this]
    exact iter_dec v ‹(τ x).head! = v₁›
  case h_2 u _ /- (τ y).head! < 0 -/  =>
    simp only [← eval_inc_dec_evalI]
    have : v₂ = Int.negSucc u := by
      { rw [← ‹(τ y).head! = v₂›, ‹(τ y).head! = Int.negSucc u›] }; rw [this]
    have : v₁ - Int.negSucc u = v₁ + Int.ofNat u.succ := by
      { simp [Int.negSucc_coe]; linarith }; rw [this]
    exact iter_inc u.succ ‹(τ x).head! = v₁›


theorem ev_invariant {x y ev : ident} {τ : SCORE.store} : x ≠ ev → y ≠ ev → (τ x).head! = v₁ → (τ y).head! = v₂ → (τ ev).head! = 0 → (τ ev) = ((eval (L2S' ev (LOOP.com.ASN x y)) τ) ev) := by
  intros
  rw [L2S', eval, eval, eval]
  rw [for_inc ‹(τ ev).head! = 0› ‹(τ y).head! = v₂›, zero_add]
  rw [eval]
  have : ([ev ↦ (v₂ :: (τ ev).tail!)]τ) x = τ x := by
    { simp [‹x ≠ ev›.symm] }; rw [this]
  have head_x : (([x ↦ (0 :: τ x)][ev ↦ (v₂ :: (τ ev).tail!)]τ) x).head! = 0 := by
    simp [List.head!]
  have head_ev : (([x ↦ (0 :: τ x)][ev ↦ (v₂ :: (τ ev).tail!)]τ) ev).head! = v₂ := by
    simp [‹x ≠ ev›, List.head!]
  rw [for_inc head_x head_ev, zero_add]
  have : (([x ↦ (0 :: τ x)][ev ↦ (v₂ :: (τ ev).tail!)]τ) x).tail! = τ x := by
    { simp }; rw [this]
  rw [SCORE.store.update_shrink]
  have head_x : (([x ↦ (v₂ :: τ x)][ev ↦ (v₂ :: (τ ev).tail!)]τ) x).head! = v₂ := by
    simp [List.head!]
  have head_ev : (([x ↦ (v₂ :: τ x)][ev ↦ (v₂ :: (τ ev).tail!)]τ) ev).head! = v₂ := by
    simp [‹x ≠ ev›, List.head!]
  rw [for_dec head_ev head_x, sub_self]
  have : (([x ↦ (v₂ :: τ x)][ev ↦ (v₂ :: (τ ev).tail!)]τ) ev).tail! = (τ ev).tail! := by
    { simp [‹x ≠ ev›] }; rw [this]
  have : ([ev ↦ (0 :: (τ ev).tail!)][x ↦ (v₂ :: τ x)][ev ↦ (v₂ :: (τ ev).tail!)]τ) ev = 0 :: (τ ev).tail! := by
    { simp }; rw [this]
  have : τ ev ≠ [] := sorry
  rewrite (config := {occs := .pos [1]}) [← List.cons_head!_tail ‹τ ev ≠ []›]
  sorry

lemma ev_zero {x y ev : ident} {τ : SCORE.store} : x ≠ ev → y ≠ ev → (τ x).head! = v₁ → (τ y).head! = v₂ → (τ ev).head! = 0 → ((eval (L2S' ev (LOOP.com.ASN x y)) τ) ev).head! = 0 := by
  intros
  have : τ ev = (eval (L2S' ev (LOOP.com.ASN x y)) τ) ev := by
    { exact ev_invariant ‹x ≠ ev› ‹y ≠ ev› ‹(τ x).head! = v₁› ‹(τ y).head! = v₂› ‹(τ ev).head! = 0› }; rw [← this]
  assumption

end L2S'

end SCORE
