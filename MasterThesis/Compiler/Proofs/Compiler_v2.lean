import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith
import MasterThesis.SCORE.Interpreter
import MasterThesis.LOOP.Interpreter
import MasterThesis.SCORE.Proofs.Language
import MasterThesis.Compiler.Compiler_v2

namespace l2s'

open SCORE Com
open LOOP Com

lemma iter_inc {x : Ident} {σ : SCORE.Store} {k : Int} (v : ℕ) : (σ x).head? = some k → (fun τ ↦ SCORE.eval (INC x) τ)^[v] σ = [x ↦ (k + ↑v) :: (σ x).tail] σ := by
  intro
  induction v
  case zero =>
    simp [Store.update_unchanged_cons ‹(σ x).head? = k›]
  case succ m ih =>
    calc
      (fun τ ↦ SCORE.eval (INC x) τ)^[m + 1] σ
      _ = eval (INC x) ((fun τ ↦ SCORE.eval (INC x) τ)^[m] σ) := by simp [Nat.add_comm m 1, Function.iterate_add_apply]
      _ = eval (INC x) ([x ↦ (k + ↑m) :: (σ x).tail] σ)       := by rw [ih]
      _ = [x ↦ (k + ↑m + 1) :: (σ x).tail] σ                  := by simp [SCORE.eval, ‹(σ x).head? = some k›]
      _ = [x ↦ (k + ↑(m + 1)) :: (σ x).tail] σ                := by
        have : k + ↑m + 1 = k + (↑m + 1) := by linarith
        simp [this]

lemma for_inc {x y : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} : (σ x).head? = v₁ → (σ y).head? = v₂ → SCORE.eval (FOR y (INC x)) σ = [x ↦ (v₁ + v₂) :: (σ x).tail] σ := by sorry

lemma for_dec {x y : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} : (σ x).head? = v₁ → (σ y).head? = v₂ → SCORE.eval (FOR y (DEC x)) σ = [x ↦ (v₁ - v₂) :: (σ x).tail] σ := by sorry

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
