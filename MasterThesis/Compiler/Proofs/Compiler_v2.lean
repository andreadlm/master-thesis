import Mathlib.Tactic.Basic
import MasterThesis.SCORE.Interpreter
import MasterThesis.LOOP.Interpreter
import MasterThesis.SCORE.Proofs.Language
import MasterThesis.Compiler.Compiler_v2

namespace l2s'

open SCORE Com
open LOOP Com

lemma for_inc {x y : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} : (σ x).head? = v₁ → (σ y).head? = v₂ → eval (FOR y (INC x)) σ = [x ↦ (v₁ + v₂) :: (σ x).tail] σ := by sorry

lemma for_dec {x y : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} : (σ x).head? = v₁ → (σ y).head? = v₂ → eval (FOR y (DEC x)) σ = [x ↦ (v₁ - v₂) :: (σ x).tail] σ := by sorry

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
