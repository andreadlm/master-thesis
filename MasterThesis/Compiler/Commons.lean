/-
"A Lean-certified reversibilization of Meyer-Ritchie LOOP language".
Master thesis in computer science, University of Turin.
Authors: Andrea Delmastro
-/
import Mathlib.Tactic.Linarith
import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language

namespace Compiler.Commons

open LOOP Com Store
open SCORE Com Store

lemma iter_inc {x : Ident} {σ : SCORE.Store} {k : Int} (v : ℕ) : (σ x).head? = k → (fun t => SCORE.eval (INC x) t)^[v] σ = σ[x ↦ (k + ↑v) :: (σ x).tail] := by
  intro
  induction v
  case zero =>
    simp [update_no_update_cons ‹(σ x).head? = k›]
  case succ m ih =>
    calc
      (fun t => SCORE.eval (INC x) t)^[m + 1] σ
      _ = eval (INC x) ((fun t => SCORE.eval (INC x) t)^[m] σ) := by
            simp [Nat.add_comm m 1, Function.iterate_add_apply]
      _ = eval (INC x) (σ[x ↦ (k + ↑m) :: (σ x).tail]) := by
            rw [ih]
      _ = σ[x ↦ (k + ↑m + 1) :: (σ x).tail] := by
            simp [SCORE.eval]
      _ = σ[x ↦ (k + ↑(m + 1)) :: (σ x).tail] := by
            have : k + ↑m + 1 = k + (↑m + 1) := by linarith
            simp [‹k + ↑m + 1 = k + (↑m + 1)›]

lemma iter_dec {x : Ident} {σ : SCORE.Store} {k : Int} (v : ℕ) : (σ x).head? = k → (fun t => SCORE.eval (DEC x) t)^[v] σ = σ[x ↦ (k - ↑v) :: (σ x).tail] := by
  intro
  induction v
  case zero =>
    simp [update_no_update_cons ‹(σ x).head? = k›]
  case succ m ih =>
    calc
      (fun t => SCORE.eval (DEC x) t)^[m + 1] σ
      _ = eval (DEC x) ((fun t => SCORE.eval (DEC x) t)^[m] σ) := by
            simp [Nat.add_comm m 1, Function.iterate_add_apply]
      _ = eval (DEC x) (σ[x ↦ (k - ↑m) :: (σ x).tail]) := by
            rw [ih]
      _ = σ[x ↦ (k - ↑m - 1) :: (σ x).tail] := by
            simp [SCORE.eval]
      _ = σ[x ↦ (k - ↑(m + 1)) :: (σ x).tail] := by
            have : k - ↑m - 1 = k - (↑m + 1) := by linarith
            simp [‹k - ↑m - 1 = k - (↑m + 1)›]

lemma for_inc {x y : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} : (σ x).head? = v₁ → (σ y).head? = v₂ → SCORE.eval (FOR y (INC x)) σ = σ[x ↦ (v₁ + v₂) :: (σ x).tail] := by
  intros
  rw [SCORE.eval]
  split
  · split
    case _ k _ =>
      calc
        (fun t => SCORE.eval (INC x) t)^[k] σ
        _ = σ[x ↦ (v₁ + ↑k) :: (σ x).tail] :=
              iter_inc k ‹(σ x).head? = v₁›
        _ = σ[x ↦ (v₁ + v₂) :: (σ x).tail] := by
              simp [Option.some.inj (Eq.trans ‹(σ y).head? = v₂›.symm ‹(σ y).head? = Int.ofNat k›)]
    case _ k _ =>
      have evalI_INC_eq_eval_DEC {x : Ident} {s : SCORE.State} : evalI (INC x) s = eval (DEC x) s := by
        cases s
        all_goals (rw [SCORE.evalI, SCORE.eval])
      calc
        (fun t => SCORE.evalI (INC x) t)^[k + 1] σ
        _ = (fun t => SCORE.eval (DEC x) t)^[k + 1] σ := by
              simp only [evalI_INC_eq_eval_DEC]
        _ = σ[x ↦ (v₁ - ↑(k + 1)) :: (σ x).tail] :=
              iter_dec (k + 1) ‹(σ x).head? = v₁›
        _ = σ[x ↦ (v₁ + v₂) :: (σ x).tail] := by
              simp [Int.sub_eq_add_neg, Int.negSucc_eq k,
                    Option.some.inj (Eq.trans ‹(σ y).head? = v₂›.symm ‹(σ y).head? = Int.negSucc k›)]
  · rw [‹(σ y).head? = v₂›] at ‹(σ y).head? = none›
    contradiction

lemma for_dec {x y : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} : (σ x).head? = v₁ → (σ y).head? = v₂ → SCORE.eval (FOR y (DEC x)) σ = σ[x ↦ (v₁ - v₂) :: (σ x).tail] := by
  intros
  rw [SCORE.eval]
  split
  · split
    case _ k _ =>
      calc
        (fun t ↦ SCORE.eval (DEC x) t)^[k] σ
        _ = σ[x ↦ (v₁ - ↑k) :: (σ x).tail] :=
              iter_dec k ‹(σ x).head? = v₁›
        _ = σ[x ↦ (v₁ - v₂) :: (σ x).tail] := by
              simp [Option.some.inj (Eq.trans ‹(σ y).head? = v₂›.symm ‹(σ y).head? = some ↑k›)]
    case _ k _ =>
      have evalI_DEC_eq_eval_INC {x : Ident} {s : SCORE.State} : evalI (DEC x) s = eval (INC x) s := by
        cases s
        all_goals (rw [SCORE.evalI, SCORE.eval])
      calc
        (fun t => SCORE.evalI (DEC x) t)^[k + 1] σ
        _ = (fun t => SCORE.eval (INC x) t)^[k + 1] σ := by
              simp only [evalI_DEC_eq_eval_INC]
        _ = σ[x ↦ (v₁ + ↑(k + 1)) :: (σ x).tail] :=
              iter_inc (k + 1) ‹(σ x).head? = v₁›
        _ = σ[x ↦ (v₁ - v₂) :: (σ x).tail] := by
              simp [Int.sub_eq_add_neg, Int.negSucc_eq k,
                    Option.some.inj (Eq.trans ‹(σ y).head? = v₂›.symm ‹(σ y).head? = Int.negSucc k›)]
  · rw [‹(σ y).head? = v₂›] at ‹(σ y).head? = none›
    contradiction

end Compiler.Commons
