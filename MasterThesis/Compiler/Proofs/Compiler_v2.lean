import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith
import MasterThesis.SCORE.Interpreter
import MasterThesis.LOOP.Interpreter
import MasterThesis.SCORE.Proofs.Language
import MasterThesis.Compiler.Compiler_v2

namespace l2s'

open SCORE Com
open LOOP Com

lemma iter_inc {x : Ident} {σ : SCORE.Store} {k : Int} (v : ℕ) : (σ x).head? = some k → (fun t ↦ SCORE.eval (INC x) t)^[v] σ = [x ↦ (k + ↑v) :: (σ x).tail] σ := by
  intro
  induction v
  case zero =>
    simp [Store.update_unchanged_cons ‹(σ x).head? = k›]
  case succ m ih =>
    calc
      (fun t => SCORE.eval (INC x) t)^[m + 1] σ
      _ = eval (INC x) ((fun t => SCORE.eval (INC x) t)^[m] σ) := by simp [Nat.add_comm m 1, Function.iterate_add_apply]
      _ = eval (INC x) ([x ↦ (k + ↑m) :: (σ x).tail] σ)       := by rw [ih]
      _ = [x ↦ (k + ↑m + 1) :: (σ x).tail] σ                  := by simp [SCORE.eval, ‹(σ x).head? = some k›]
      _ = [x ↦ (k + ↑(m + 1)) :: (σ x).tail] σ                := by
        have : k + ↑m + 1 = k + (↑m + 1) := by linarith
        simp [this]

lemma iter_dec {x : Ident} {σ : SCORE.Store} {k : Int} (v : ℕ) : (σ x).head? = some k → (fun t ↦ SCORE.eval (DEC x) t)^[v] σ = [x ↦ (k - ↑v) :: (σ x).tail] σ := by
  intro
  induction v
  case zero =>
    simp [Store.update_unchanged_cons ‹(σ x).head? = k›]
  case succ m ih =>
    calc
      (fun t => SCORE.eval (DEC x) t)^[m + 1] σ
      _ = eval (DEC x) ((fun t => SCORE.eval (DEC x) t)^[m] σ) := by simp [Nat.add_comm m 1, Function.iterate_add_apply]
      _ = eval (DEC x) ([x ↦ (k - ↑m) :: (σ x).tail] σ)       := by rw [ih]
      _ = [x ↦ (k - ↑m - 1) :: (σ x).tail] σ                  := by simp [SCORE.eval, ‹(σ x).head? = some k›]
      _ = [x ↦ (k - ↑(m + 1)) :: (σ x).tail] σ                := by
        have : k - ↑m - 1 = k - (↑m + 1) := by linarith
        simp [this]

lemma for_inc {x y : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} : (σ x).head? = v₁ → (σ y).head? = v₂ → SCORE.eval (FOR y (INC x)) σ = [x ↦ (v₁ + v₂) :: (σ x).tail] σ := by
  intros
  rw [SCORE.eval]
  split
  · split
    case _ k _ =>
      calc
        (fun t => SCORE.eval (INC x) t)^[k] σ
        _ = [x ↦ (v₁ + ↑k) :: (σ x).tail] σ := iter_inc k ‹(σ x).head? = some v₁›
        _ = [x ↦ (v₁ + v₂) :: (σ x).tail] σ := by simp [Option.some.inj (Eq.trans ‹(σ y).head? = some v₂›.symm ‹(σ y).head? = some (Int.ofNat k)›)]
    case _ k _ =>
      have evalI_INC_eq_eval_DEC {x : Ident} {s : SCORE.State} : evalI (INC x) s = eval (DEC x) s := by
        cases Option.eq_none_or_eq_some s
        · rw [‹s = none›, SCORE.evalI, SCORE.eval]
        · cases ‹∃ x, s = some x› with
          | intro σ _ => rw [‹s = some σ›, SCORE.evalI, SCORE.eval]
      calc
        (fun t => SCORE.evalI (INC x) t)^[k + 1] σ
        _ = (fun t => SCORE.eval (DEC x) t)^[k + 1] σ := by simp only [evalI_INC_eq_eval_DEC]
        _ = [x ↦ (v₁ - ↑(k + 1)) :: (σ x).tail] σ     := by exact iter_dec (k + 1) ‹(σ x).head? = some v₁›
        _ = [x ↦ (v₁ + v₂) :: (σ x).tail] σ           := by simp [Int.sub_eq_add_neg, Int.negSucc_eq k,
                                                                  Option.some.inj (Eq.trans ‹(σ y).head? = some v₂›.symm ‹(σ y).head? = some (Int.negSucc k)›)]
  · rw [‹(σ y).head? = some v₂›] at ‹(σ y).head? = none›
    contradiction

lemma for_dec {x y : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} : (σ x).head? = v₁ → (σ y).head? = v₂ → SCORE.eval (FOR y (DEC x)) σ = [x ↦ (v₁ - v₂) :: (σ x).tail] σ := by
  intros
  rw [SCORE.eval]
  split
  · split
    case _ k _ =>
      calc
        (fun t => SCORE.eval (DEC x) t)^[k] σ
        _ = [x ↦ (v₁ - ↑k) :: (σ x).tail] σ := iter_dec k ‹(σ x).head? = some v₁›
        _ = [x ↦ (v₁ - v₂) :: (σ x).tail] σ := by simp [Option.some.inj (Eq.trans ‹(σ y).head? = some v₂›.symm ‹(σ y).head? = some (Int.ofNat k)›)]
    case _ k _ =>
      have evalI_DEC_eq_eval_INC {x : Ident} {s : SCORE.State} : evalI (DEC x) s = eval (INC x) s := by
        cases Option.eq_none_or_eq_some s
        · rw [‹s = none›, SCORE.evalI, SCORE.eval]
        · cases ‹∃ x, s = some x› with
          | intro σ _ => rw [‹s = some σ›, SCORE.evalI, SCORE.eval]
      calc
        (fun t => SCORE.evalI (DEC x) t)^[k + 1] σ
        _ = (fun t => SCORE.eval (INC x) t)^[k + 1] σ := by simp only [evalI_DEC_eq_eval_INC]
        _ = [x ↦ (v₁ + ↑(k + 1)) :: (σ x).tail] σ     := by exact iter_inc (k + 1) ‹(σ x).head? = some v₁›
        _ = [x ↦ (v₁ - v₂) :: (σ x).tail] σ           := by simp [Int.sub_eq_add_neg, Int.negSucc_eq k,
                                                                  Option.some.inj (Eq.trans ‹(σ y).head? = some v₂›.symm ‹(σ y).head? = some (Int.negSucc k)›)]
  · rw [‹(σ y).head? = some v₂›] at ‹(σ y).head? = none›
    contradiction

lemma ev_invariant {x y ev : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} : x ≠ ev → y ≠ ev → (σ x).head? = v₁ → (σ y).head? = v₂ → (σ ev).head? = some 0 → ∃ (σ' : SCORE.Store), (eval (l2s' ev (ASN x y)) σ = σ' ∧ (σ' ev).head? = some 0) := by
  intros
  repeat constructor
  · rw [l2s']
    calc
      eval (l2s' ev (ASN x y)) σ
      _ = eval (FOR y (INC ev);; CON x;; FOR ev (INC x);; FOR x (DEC ev)) σ                    := by simp [l2s']
      _ = eval (CON x;; FOR ev (INC x);; FOR x (DEC ev)) ([ev ↦ v₂ :: (σ ev).tail] σ)          := by simp [SCORE.eval, for_inc ‹(σ ev).head? = some 0› ‹(σ y).head? = v₂›]
      _ = eval (FOR ev (INC x);; FOR x (DEC ev)) ([x ↦ 0 :: (σ x)] [ev ↦ v₂ :: (σ ev).tail] σ) := by simp [SCORE.eval, ‹x ≠ ev›.symm]
      _ = eval (FOR x (DEC ev)) ([x ↦ v₂ :: σ x] [ev ↦ v₂ :: (σ ev).tail] σ)                   := by
        have head_x : (([x ↦ 0 :: (σ x)] [ev ↦ v₂ :: (σ ev).tail] σ) x).head? = some 0 := by simp
        have head_ev : (([x ↦ 0 :: (σ x)] [ev ↦ v₂ :: (σ ev).tail] σ) ev).head? = v₂ := by simp [‹x ≠ ev›]
        simp [SCORE.eval, for_inc head_x head_ev]
      _ = [ev ↦ 0 :: (σ ev).tail] [x ↦ (v₂ :: σ x)] [ev ↦ v₂ :: (σ ev).tail] σ                 := by
        have head_x : (([x ↦ v₂ :: σ x] [ev ↦ v₂ :: (σ ev).tail] σ) x).head? = v₂ := by simp
        have head_ev : (([x ↦ v₂ :: σ x] [ev ↦ v₂ :: (σ ev).tail] σ) ev).head? = v₂ := by simp [‹x ≠ ev›]
        simp [SCORE.eval, for_dec head_ev head_x, ‹x ≠ ev›]
  · simp
