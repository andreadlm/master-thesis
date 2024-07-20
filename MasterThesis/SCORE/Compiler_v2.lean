import MasterThesis.SCORE.Language
import MasterThesis.SCORE.Interpreter
import MasterThesis.LOOP.Language
import MasterThesis.LOOP.Interpreter
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Basic

namespace SCORE

open SCORE.Com

def L2S' (ev : Ident) (Lc: LOOP.Com) : SCORE.Com :=
  match Lc with
  | LOOP.Com.SKIP    => SKIP
  | LOOP.Com.ZER x   => CON x
  | LOOP.Com.ASN x y => FOR y (INC ev) ;;
                        CON x ;;
                        FOR ev (INC x) ;;
                        FOR x (DEC ev)
  | LOOP.Com.INC x   => INC x
  | LOOP.Com.SEQ P Q => L2S' ev P ;;
                        L2S' ev Q
  | LOOP.Com.FOR x P => FOR x (L2S' ev P)

namespace L2S'

example : - Int.negSucc u = Int.ofNat u.succ := by simp [Int.negSucc_coe]

-- TODO: sostituire con un teorema più generale sulla reversibilità?
lemma eval_inc_dec_evalI {x : Ident} {σ : SCORE.Store} : eval (INC x) σ = evalI (DEC x) σ := by
  rw [SCORE.eval, SCORE.evalI]

-- TODO: sostituire con un teorema più generale sulla reversibilità?
lemma eval_dec_inc_evalI {x : Ident} {σ : SCORE.Store} : eval (DEC x) σ = evalI (INC x) σ := by
  rw [SCORE.eval, SCORE.evalI]

lemma iter_inc {x : Ident} {σ : SCORE.Store} {k : Int} (v : ℕ) : (σ x).head? = some k → (fun τ ↦ eval (INC x) τ)^[v] σ = [x ↦ ((k + Int.ofNat v) :: (σ x).tail)]σ := by
  intros
  induction v generalizing σ with
  | zero      =>
    have : (fun τ ↦ eval (INC x) τ)^[0] σ = σ := by
      { simp }; rw [this]
    have : (k + Int.ofNat 0) = k := by
      { simp }; rw [this]
    exact SCORE.Store.update_unchanged_cons ‹(σ x).head? = k›
  | succ m ih =>
    have : (fun τ ↦ eval (INC x) τ)^[m + 1] σ = eval (INC x) ((fun τ ↦ eval (INC x) τ)^[m] σ) := by
      { simp [Nat.add_comm m 1, Function.iterate_add_apply] }; rw[this]
    rw [ih ‹(σ x).head? = k›, SCORE.eval]
    have : (([x ↦ ((k + Int.ofNat m) :: (σ x).tail)]σ) x).head? = some (k + Int.ofNat m) := by
      { simp }; rw [this]
    split
    case succ.h_1 v _ =>
      have : v = k + Int.ofNat m := by
        { exact (Option.some.inj ‹some (k + Int.ofNat m) = some v›).symm }; rw [this]
      have : (([x ↦ ((k + Int.ofNat m) :: (σ x).tail)]σ) x).tail = (σ x).tail := by
        { simp }; rw [this]
      rw [SCORE.Store.update_shrink]
      funext y
      cases eq_or_ne x y with
    | inl =>
      rw [← ‹x = y›]
      have : ([x ↦ ((k + Int.ofNat m + 1) :: (σ x).tail)]σ) x = ((k + Int.ofNat m + 1) :: (σ x).tail) := by
        { simp }; rw [this]
      have : ([x ↦ ((k + Int.ofNat (m + 1)) :: (σ x).tail)]σ) x = ((k + (Int.ofNat m + 1)) :: (σ x).tail) := by
        { simp }; rw [this]
      have : (k + Int.ofNat m + 1) = (k + (Int.ofNat m + 1)) := by
        { linarith }; rw [this]
    | inr =>
      have : ([x ↦ ((k + Int.ofNat m + 1) :: (σ x).tail)]σ) y = σ y := by
        { simp [‹x ≠ y›] }; rw [this]
      have : ([x ↦ ((k + Int.ofNat (m + 1)) :: (σ x).tail)]σ) y = σ y := by
        { simp [‹x ≠ y›] }; rw [this]
    case succ.h_2     => contradiction

lemma iter_dec {x : Ident} {σ: SCORE.Store} {k : Int} (v : ℕ) : (σ x).head? = some k → (fun τ ↦ eval (DEC x) τ)^[v] σ = [x ↦ ((k - Int.ofNat v) :: (σ x).tail)]σ := sorry

lemma for_inc {x y : Ident} {v₁ v₂ : Int} {τ : SCORE.Store} : (τ x).head? = some v₁ → (τ y).head? = some v₂ → eval (FOR y (INC x)) τ = [x ↦ ((v₁ + v₂) :: (τ x).tail)]τ := by
  intros
  rw [SCORE.eval]
  split
  case h_1 v _ /- (τ y).head? = some v -/ =>
    split
    case h_1 k _ /- (τ y).head! >= 0 -/ =>
      have : v₂ = Int.ofNat k := by
        { rw [‹(τ y).head? = some v₂›] at ‹(τ y).head? = some (Int.ofNat k)›
          exact Option.some.inj ‹some v₂ = some (Int.ofNat k)›
        }; rw [this]
      exact iter_inc k ‹(τ x).head? = some v₁›
    case h_2 k _ /- (τ y).head! < 0 -/  =>
      simp only [← eval_dec_inc_evalI]
      have : v₂ = Int.negSucc k := by
        { rw [‹(τ y).head? = some v₂›] at ‹(τ y).head? = some (Int.negSucc k)›
          exact Option.some.inj ‹some v₂ = some (Int.negSucc k)›
        }; rw [this]
      have : v₁ + Int.negSucc k = v₁ - Int.ofNat k.succ := by
        { simp [Int.negSucc_coe]
          linarith
        }; rw [this]
      exact iter_dec k.succ ‹(τ x).head? = some v₁›
  case h_2     /- (τ y).head? = none -/   =>
    rw [‹(τ y).head? = some v₂›] at ‹(τ y).head? = none›
    contradiction

lemma for_dec {x y : Ident} {v₁ v₂ : Int} {τ : SCORE.Store} : (τ x).head? = some v₁ → (τ y).head? = some v₂ → eval (FOR y (DEC x)) τ = [x ↦ ((v₁ - v₂) :: (τ x).tail)]τ := by
  intros
  rw [SCORE.eval]
  split
  case h_1 v _ /- (τ y).head? = some v -/ =>
    split
    case h_1 k _ /- (τ y).head! >= 0 -/ =>
      have : v₂ = Int.ofNat k := by
        { rw [‹(τ y).head? = some v₂›] at ‹(τ y).head? = some (Int.ofNat k)›
          exact Option.some.inj ‹some v₂ = some (Int.ofNat k)›
        }; rw [this]
      exact iter_dec k ‹(τ x).head? = some v₁›
    case h_2 k _ /- (τ y).head! < 0 -/  =>
      simp only [← eval_inc_dec_evalI]
      have : v₂ = Int.negSucc k := by
        { rw [‹(τ y).head? = some v₂›] at ‹(τ y).head? = some (Int.negSucc k)›
          exact Option.some.inj ‹some v₂ = some (Int.negSucc k)›
        }; rw [this]
      have : v₁ - Int.negSucc k = v₁ + Int.ofNat k.succ := by
        { simp [Int.negSucc_coe]
          linarith
        }; rw [this]
      exact iter_inc k.succ ‹(τ x).head? = some v₁›
  case h_2     /- (τ y).head? = none -/   =>
    rw [‹(τ y).head? = some v₂›] at ‹(τ y).head? = none›
    contradiction

theorem ev_invariant {x y ev : Ident} {τ : SCORE.Store} : x ≠ ev → y ≠ ev → (τ x).head? = some v₁ → (τ y).head? = some v₂ → (τ ev).head? = some 0 → (τ ev) = ((eval (L2S' ev (LOOP.Com.ASN x y)) τ) ev) := by
  intros
  rw [L2S', eval, eval, eval]
  rw [for_inc ‹(τ ev).head? = some 0› ‹(τ y).head? = some v₂›, zero_add]
  rw [eval]
  have : ([ev ↦ (v₂ :: (τ ev).tail)]τ) x = τ x := by
    { simp [‹x ≠ ev›.symm] }; rw [this]
  have head_x' : (([x ↦ (0 :: τ x)][ev ↦ (v₂ :: (τ ev).tail)]τ) x).head? = some 0 := by
    simp
  have head_ev' : (([x ↦ (0 :: τ x)][ev ↦ (v₂ :: (τ ev).tail)]τ) ev).head? = some v₂ := by
    simp [‹x ≠ ev›]
  rw [for_inc head_x' head_ev', zero_add]
  have : (([x ↦ (0 :: τ x)][ev ↦ (v₂ :: (τ ev).tail)]τ) x).tail = τ x := by
    { simp }; rw [this]
  rw [SCORE.Store.update_shrink]
  have head_x'' : (([x ↦ (v₂ :: τ x)][ev ↦ (v₂ :: (τ ev).tail)]τ) x).head? = some v₂ := by
    simp
  have head_ev'' : (([x ↦ (v₂ :: τ x)][ev ↦ (v₂ :: (τ ev).tail)]τ) ev).head? = some v₂ := by
    simp [‹x ≠ ev›]
  rw [for_dec head_ev'' head_x'', sub_self]
  have : (([x ↦ (v₂ :: τ x)][ev ↦ (v₂ :: (τ ev).tail)]τ) ev).tail = (τ ev).tail := by
    { simp [‹x ≠ ev›] }; rw [this]
  have : ([ev ↦ (0 :: (τ ev).tail)][x ↦ (v₂ :: τ x)][ev ↦ (v₂ :: (τ ev).tail)]τ) ev = 0 :: (τ ev).tail := by
    { simp }; rw [this]
  have : 0 ∈ (τ ev).head? := by
    simpa
  exact (List.cons_head?_tail ‹0 ∈ (τ ev).head?›).symm

lemma ev_zero {x y ev : Ident} {τ : SCORE.Store} : x ≠ ev → y ≠ ev → (τ x).head? = some v₁ → (τ y).head? = some v₂ → (τ ev).head? = some 0 → ((eval (L2S' ev (LOOP.Com.ASN x y)) τ) ev).head? = some 0 := by
  intros
  have : τ ev = (eval (L2S' ev (LOOP.Com.ASN x y)) τ) ev := by
    { exact ev_invariant ‹x ≠ ev› ‹y ≠ ev› ‹(τ x).head? = some v₁› ‹(τ y).head? = some v₂› ‹(τ ev).head? = some 0› }; rw [← this]
  assumption

end L2S'

end SCORE
