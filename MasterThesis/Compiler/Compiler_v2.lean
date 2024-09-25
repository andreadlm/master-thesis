/-
"A Lean-certified reversibilization of Meyer-Ritchie LOOP language".
Master thesis in computer science, University of Turin.
Authors: Andrea Delmastro
-/
import Mathlib.Tactic.Linarith
import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language

/-!
# Compiler for LOOP language, version 2
-/

namespace Compiler

open LOOP Com
open SCORE Com

namespace v2

def l2s (ev : Ident) (P : LOOP.Com) : SCORE.Com :=
  CON ev;;
  match P with
  | .SKIP     => SKIP
  | .ZER x    => CON x
  | .ASN x y  => FOR y (INC ev);;
                 CON x;;
                 FOR ev (INC x);;
                 FOR x (DEC ev)
  | .INC x    => INC x
  | .SEQ P Q  => l2s ev P;;
                 l2s ev Q
  | .LOOP x P => FOR x (l2s ev P)

end v2

open v2

def eq_states_idents (s : LOOP.State) (t : SCORE.State) (ids : Finset Ident) : Prop :=
  match s, t with
  | some σ, some τ => ∀ (x : Ident), x ∈ ids → some ↑(σ x) = (τ x).head?
  | _     , _      => False

notation:50 s:50 "∼[" P:50 "]" t:50 => eq_states_idents s t P

lemma eq_states_idents_subs {s : LOOP.State} {t : SCORE.State} {a b : Finset Ident} : s ∼[a ∪ b] t → s ∼[a] t := by
  intro eqs
  cases s <;> cases t
  case some.some σ τ =>
    intros x _
    exact ‹σ ∼[a ∪ b] τ› x (Finset.mem_union_left b ‹x ∈ a›)
  all_goals (simp [eq_states_idents] at eqs)

lemma iter_inc {x : Ident} {σ : SCORE.Store} {k : Int} (v : ℕ) : (σ x).head? = k → (fun t => SCORE.eval (INC x) t)^[v] σ = σ[x ↦ (k + ↑v) :: (σ x).tail] := by
  intro
  induction v
  case zero =>
    simp [Store.update_no_update_cons ‹(σ x).head? = k›]
  case succ m ih =>
    calc
      (fun t => SCORE.eval (INC x) t)^[m + 1] σ
      _ = eval (INC x) ((fun t => SCORE.eval (INC x) t)^[m] σ) := by
            simp [Nat.add_comm m 1, Function.iterate_add_apply]
      _ = eval (INC x) (σ[x ↦ (k + ↑m) :: (σ x).tail]) := by
            rw [ih]
      _ = σ[x ↦ (k + ↑m + 1) :: (σ x).tail] := by
            simp [SCORE.eval, ‹(σ x).head? = k›]
      _ = σ[x ↦ (k + ↑(m + 1)) :: (σ x).tail] := by
            have : k + ↑m + 1 = k + (↑m + 1) := by linarith
            simp [this]

lemma iter_dec {x : Ident} {σ : SCORE.Store} {k : Int} (v : ℕ) : (σ x).head? = k → (fun t => SCORE.eval (DEC x) t)^[v] σ = σ[x ↦ (k - ↑v) :: (σ x).tail] := by
  intro
  induction v
  case zero =>
    simp [Store.update_no_update_cons ‹(σ x).head? = k›]
  case succ m ih =>
    calc
      (fun t => SCORE.eval (DEC x) t)^[m + 1] σ
      _ = eval (DEC x) ((fun t => SCORE.eval (DEC x) t)^[m] σ) := by
            simp [Nat.add_comm m 1, Function.iterate_add_apply]
      _ = eval (DEC x) (σ[x ↦ (k - ↑m) :: (σ x).tail]) := by
            rw [ih]
      _ = σ[x ↦ (k - ↑m - 1) :: (σ x).tail] := by
            simp [SCORE.eval, ‹(σ x).head? = k›]
      _ = σ[x ↦ (k - ↑(m + 1)) :: (σ x).tail] := by
            have : k - ↑m - 1 = k - (↑m + 1) := by linarith
            simp [this]

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
              simp [Option.some.inj (Eq.trans ‹(σ y).head? = v₂›.symm ‹(σ y).head? = some ↑k›)]
    case _ k _ =>
      have evalI_INC_eq_eval_DEC {x : Ident} {s : SCORE.State} : evalI (INC x) s = eval (DEC x) s := by
        cases Option.eq_none_or_eq_some s
        · rw [‹s = none›, SCORE.evalI, SCORE.eval]
        · cases ‹∃ x, s = some x› with
          | intro σ _ => rw [‹s = σ›, SCORE.evalI, SCORE.eval]
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
        cases Option.eq_none_or_eq_some s
        · rw [‹s = none›, SCORE.evalI, SCORE.eval]
        · cases ‹∃ x, s = some x› with
          | intro σ _ => rw [‹s = σ›, SCORE.evalI, SCORE.eval]
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

lemma ev_invariant {x y ev : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} (h : ev ∉ (ASN x y).ids) : (σ x).head? = v₁ → (σ y).head? = v₂ → ∃ (σ' : SCORE.Store), (eval (l2s ev (ASN x y)) σ = σ' ∧ (σ' ev).head? = some 0) := by
  intros
  have : ev ≠ x ∧ ev ≠ y := by simpa [ids] using ‹ev ∉ (ASN x y).ids›
  have ⟨_, _⟩ := ‹ev ≠ x ∧ ev ≠ y›
  constructor
  · constructor
    · calc
        eval (l2s ev (ASN x y)) σ
        _ = eval (CON ev;; FOR y (INC ev);; CON x;; FOR ev (INC x);; FOR x (DEC ev)) σ := by
              simp [l2s]
        _ = eval (FOR y (INC ev);; CON x;; FOR ev (INC x);; FOR x (DEC ev)) (σ[ev ↦ 0 :: σ ev]) := by
              simp [SCORE.eval]
        _ = eval (CON x;; FOR ev (INC x);; FOR x (DEC ev)) (eval (FOR y (INC ev)) (σ[ev ↦ 0 :: σ ev])) := by
              simp [SCORE.eval]
        _ = eval (CON x;; FOR ev (INC x);; FOR x (DEC ev)) (σ[ev ↦ v₂ :: σ ev]) := by
              have : ((σ[ev ↦ 0 :: σ ev]) ev).head? = some 0 := by simp
              have : ((σ[ev ↦ 0 :: σ ev]) y).head? = v₂ := by simp [‹ev ≠ y›, ‹(σ y).head? = v₂›]
              simp [for_inc ‹((σ[ev ↦ 0 :: σ ev]) ev).head? = some 0› ‹((σ[ev ↦ 0 :: σ ev]) y).head? = v₂›]
        _ = eval (FOR ev (INC x);; FOR x (DEC ev)) (σ[ev ↦ v₂ :: σ ev][x ↦ 0 :: σ x]) := by
              simp[SCORE.eval, ‹ev ≠ x›]
        _ = eval (FOR x (DEC ev)) (eval (FOR ev (INC x)) (σ[ev ↦ v₂ :: σ ev][x ↦ 0 :: σ x])) := by
              simp [SCORE.eval]
        _ = eval (FOR x (DEC ev)) (σ[ev ↦ v₂ :: σ ev][x ↦ v₂ :: σ x]) := by
              have : ((σ[ev ↦ v₂ :: σ ev][x ↦ 0 :: σ x]) x).head? = some 0 := by simp
              have : ((σ[ev ↦ v₂ :: σ ev][x ↦ 0 :: σ x]) ev).head? = v₂ := by simp [‹ev ≠ x›.symm]
              simp [for_inc ‹((σ[ev ↦ v₂ :: σ ev][x ↦ 0 :: σ x]) x).head? = some 0› ‹((σ[ev ↦ v₂ :: σ ev][x ↦ 0 :: σ x]) ev).head? = v₂›]
        _ = σ[x ↦ v₂ :: σ x][ev ↦ 0 :: σ ev] := by
              have : ((σ[ev ↦ v₂ :: σ ev][x ↦ v₂ :: σ x]) ev).head? = v₂ := by simp [‹ev ≠ x›.symm]
              have : ((σ[ev ↦ v₂ :: σ ev][x ↦ v₂ :: σ x]) x).head? = v₂ := by simp
              simp [for_dec ‹((σ[ev ↦ v₂ :: σ ev][x ↦ v₂ :: σ x]) ev).head? = v₂› ‹((σ[ev ↦ v₂ :: σ ev][x ↦ v₂ :: σ x]) x).head? = v₂›, ‹ev ≠ x›.symm, Store.update_swap ‹ev ≠ x›.symm]
    · simp

end Compiler
