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

lemma inc_iter {x : ident} {σ: SCORE.store} {k : Int} (v : ℕ) : (σ x).head! = k → (fun τ ↦ eval (INC x) τ)^[v] σ = [x ↦ ((k + Int.ofNat v) :: (σ x).tail!)]σ := by
  intros
  induction v generalizing σ with
  | zero      =>
    have : (fun τ ↦ eval (INC x) τ)^[0] σ = σ := by
      { simp }; rw [this]
    have : (k + Int.ofNat 0) = k := by
      { simp }; rw [this]
    apply SCORE.store.update_unchanged_cons ‹(σ x).head! = k›
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

lemma inc_iter_inv {x : ident} {σ: SCORE.store} {k : Int} (v : ℕ) : (σ x).head! = k → (fun τ ↦ evalI (INC x) τ)^[v] σ = [x ↦ ((k + Int.negSucc (v - 1)) :: (σ x).tail!)]σ := sorry

lemma for_inc {x y : ident} {v₁ v₂ : Int} {τ : SCORE.store} : (τ x).head! = v₁ → (τ y).head! = v₂ → eval (FOR y (INC x)) τ = [x ↦ ((v₁ + v₂) :: (τ x).tail!)]τ := by
  intros
  rw [SCORE.eval]
  split
  case h_1 v _ /- (τ y).head! >= 0 -/ =>
    have : v₂ = Int.ofNat v := by
      { rw [← ‹(τ y).head! = v₂›, ‹(τ y).head! = Int.ofNat v›] }; rw [this]
    apply inc_iter v ‹(τ x).head! = v₁›
  case h_2 u _ /- (τ y).head! < 0  -/ =>
    have : v₂ = Int.negSucc u := by
      { rw [← ‹(τ y).head! = v₂›, ‹(τ y).head! = Int.negSucc u›] }; rw [this]
    apply inc_iter_inv u.succ ‹(τ x).head! = v₁›

lemma for_dec (x y : ident) (v₁ v₂ : Int) (τ : SCORE.store) : (τ x).head! = v₁ → (τ y).head! = v₂ → eval (FOR y (DEC x)) τ = [x ↦ ((v₁ - v₂) :: (τ x).tail!)]τ := sorry

lemma evaluation_invariant (x y ev : ident) (τ : SCORE.store) : x ≠ ev → y ≠ ev → (τ x).head! = v₁ → (τ y).head! = v₂ → (τ ev).head! = v₃ → (τ ev) = ((eval (L2S' ev (LOOP.com.ASN x y)) τ) ev) := by
  intros
  rewrite [L2S']
  rewrite [eval]
  rewrite [eval]
  rewrite [eval]
  rewrite [for_inc ‹(τ ev).head! = v₃› ‹(τ y).head! = v₂›]
  rewrite [eval]
  rewrite [SCORE.store.update_other]
  have h1 : (([x ↦ (0 :: τ x)][ev ↦ ((v₃ + v₂) :: (τ ev).tail!)]τ) x).head! = 0 := sorry
  have h2 : (([x ↦ (0 :: τ x)][ev ↦ ((v₃ + v₂) :: (τ ev).tail!)]τ) ev).head! = (v₃ + v₂) := sorry
  rewrite [for_inc h1 h2]
  simp
  have h3 : (([x ↦ ((v₃ + v₂) :: τ x)][x ↦ (0 :: τ x)][ev ↦ ((v₃ + v₂) :: (τ ev).tail!)]τ) ev).head! = (v₃ + v₂) := sorry
  have h4 : (([x ↦ ((v₃ + v₂) :: τ x)][x ↦ (0 :: τ x)][ev ↦ ((v₃ + v₂) :: (τ ev).tail!)]τ) x).head! = (v₃ + v₂) := sorry
  rewrite [for_dec ev x (v₃ + v₂) (v₃ + v₂) ([x ↦ ((v₃ + v₂) :: τ x)][x ↦ (0 :: τ x)][ev ↦ ((v₃ + v₂) :: (τ ev).tail!)]τ) h3 h4]
  simp
  sorry
  sorry

lemma evaluation_zero (x y ev : ident) (τ : SCORE.store) : (τ ev).head! = 0 → ((eval (L2S' ev (LOOP.com.ASN x y)) τ) ev).head! = 0 := by
  sorry -- intro; simpa only [← evaluation_invariant x y ev τ]

/- lemma iterate_lemma (x : ident) (σ γ : SCORE.store) (k : Int) (v : ℕ) : (σ x).head! = k -> (fun τ ↦ eval (INC x) τ)^[v] σ = γ -> (γ x).head! = v + k := by
  intros h1 h2
  induction v generalizing γ with
  | zero =>
    rw[← h1]
    simp
    simp at h2
    rw[h2]
  | succ m ih =>
    simp only [Nat.add_comm m 1, Function.iterate_add_apply] at h2
    simp at h2 -/



/- lemma for_inc (x y : ident) (v₁ v₂ : Int) (τ : SCORE.store) : (τ x).head! = v₁ → (τ y).head! = v₂ → eval (FOR y (INC x)) τ = [x ↦ ((v₁ + v₂) :: (τ x).tail!)]τ := by
  intros
  rewrite [SCORE.eval]
  split
  case h_1 xv1 yv2 xisInt v vPos =>
    clear vPos
    induction v with
    | zero =>
      simp
      funext
      sorry
    | succ m ih =>
      simp only [Nat.add_comm m 1, Function.iterate_add_apply]
      rewrite [ih]
      simp
      rewrite [SCORE.eval]
      simp [List.head!]
  case h_2 _ v => sorry -/

end L2S'

end SCORE
