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

open LOOP Com Store
open SCORE Com Store

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

notation:50 s:50 " ∼[" P:50 "] " t:50 => eq_states_idents s t P

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
    simp [update_no_update_cons ‹(σ x).head? = k›]
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
    simp [update_no_update_cons ‹(σ x).head? = k›]
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

lemma ev_invariant {x y ev : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} (h : ev ∉ (ASN x y).ids) : (σ x).head? = v₁ → (σ y).head? = v₂ → ∃ (σ' : SCORE.Store), (eval (l2s ev (ASN x y)) σ = σ' ∧ (σ' ev).head? = some 0) := by
  intros
  have ⟨_, _⟩ : ev ≠ x ∧ ev ≠ y := by simpa [ids] using ‹ev ∉ (ASN x y).ids›
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
              simp [for_dec ‹((σ[ev ↦ v₂ :: σ ev][x ↦ v₂ :: σ x]) ev).head? = v₂› ‹((σ[ev ↦ v₂ :: σ ev][x ↦ v₂ :: σ x]) x).head? = v₂›, ‹ev ≠ x›.symm, update_swap ‹ev ≠ x›.symm]
    · simp

theorem soundness_ext {s : LOOP.State} {t : SCORE.State} {ev : Ident} {ext : Finset Ident} (P : LOOP.Com) : ev ∉ (P.ids ∪ ext) → s ∼[P.ids ∪ ext] t → (LOOP.eval P s) ∼[P.ids ∪ ext] (SCORE.eval (l2s ev P) t) := by
  intros h_ev eqs
  induction P generalizing s t ext
  all_goals (cases s <;> cases t <;> rw [LOOP.Com.ids] at *)
  case SKIP.some.some σ τ =>
    simp only [LOOP.eval, l2s, SCORE.eval]
    intros y _
    cases eq_or_ne y ev
    · rw [‹y = ev›] at ‹y ∈ ∅ ∪ ext›
      contradiction
    · simpa [‹y ≠ ev›.symm] using (‹σ ∼[∅ ∪ ext] τ› y ‹y ∈ ∅ ∪ ext›)
  case ZER.some.some x σ τ =>
    simp only [LOOP.eval, l2s, SCORE.eval]
    intros y _
    cases eq_or_ne x y <;> cases eq_or_ne y ev
    case inr.inr => simpa [‹x ≠ y›, ‹y ≠ ev›.symm] using (‹σ ∼[{x} ∪ ext] τ› y ‹y ∈ {x} ∪ ext›)
    case inr.inl => rw [‹y = ev›] at ‹y ∈ {x} ∪ ext›
                    contradiction
    all_goals (simp [‹x = y›])
  case ASN.some.some x y σ τ =>
    simp only [LOOP.eval, l2s]
    have ⟨_, ⟨_, _⟩⟩ : ev ≠ x ∧ ev ≠ y ∧ ev ∉ ext := by simpa using ‹ev ∉ {x, y} ∪ ext›
    calc
      eval (CON ev;; FOR y (INC ev);; CON x;; FOR ev (INC x);; FOR x (DEC ev)) τ
      _ = eval (FOR y (INC ev);; CON x;; FOR ev (INC x);; FOR x (DEC ev)) (τ[ev ↦ 0 :: τ ev]) := by
            simp [SCORE.eval]
      _ = eval (CON x;; FOR ev (INC x);; FOR x (DEC ev)) (eval (FOR y (INC ev)) (τ[ev ↦ 0 :: τ ev])) := by
            simp [SCORE.eval]
      _ = SCORE.eval (CON x;; FOR ev (INC x);; FOR x (DEC ev)) (τ[ev ↦ (σ y) :: τ ev]) := by
            have : ((τ[ev ↦ 0 :: τ ev]) ev).head? = some 0 := by simp
            have : ((τ[ev ↦ 0 :: τ ev]) y).head? = some (σ y) := by
              have : y ∈ {x, y} ∪ ext := by simp
              simpa [‹ev ≠ y›] using (‹σ ∼[{x, y} ∪ ext] τ› y ‹y ∈ {x, y} ∪ ext›).symm
            simp [for_inc ‹((τ[ev ↦ 0 :: τ ev]) ev).head? = some 0› ‹((τ[ev ↦ 0 :: τ ev]) y).head? = some (σ y)›]
      _ = eval (FOR ev (INC x);; FOR x (DEC ev)) (τ[ev ↦ (σ y) :: τ ev][x ↦ 0 :: τ x]) := by
            simp[SCORE.eval, ‹ev ≠ x›]
      _ = eval (FOR x (DEC ev)) (eval (FOR ev (INC x)) (τ[ev ↦ (σ y) :: τ ev][x ↦ 0 :: τ x])) := by
            simp [SCORE.eval]
      _ = eval (FOR x (DEC ev)) (τ[ev ↦ (σ y) :: τ ev][x ↦ (σ y) :: τ x]) := by
            have : ((τ[ev ↦ (σ y) :: τ ev][x ↦ 0 :: τ x]) x).head? = some 0 := by simp
            have : ((τ[ev ↦ (σ y) :: τ ev][x ↦ 0 :: τ x]) ev).head? = some (σ y) := by simp [‹ev ≠ x›.symm]
            simp [for_inc ‹((τ[ev ↦ (σ y) :: τ ev][x ↦ 0 :: τ x]) x).head? = some 0› ‹((τ[ev ↦ (σ y) :: τ ev][x ↦ 0 :: τ x]) ev).head? = some (σ y)›]
      _ = τ[x ↦ (σ y) :: τ x][ev ↦ 0 :: τ ev] := by
            have : ((τ[ev ↦ (σ y) :: τ ev][x ↦ (σ y) :: τ x]) ev).head? = some (σ y) := by simp [‹ev ≠ x›.symm]
            have : ((τ[ev ↦ (σ y) :: τ ev][x ↦ (σ y) :: τ x]) x).head? = some (σ y) := by simp
            simp [for_dec ‹((τ[ev ↦ (σ y) :: τ ev][x ↦ (σ y) :: τ x]) ev).head? = some (σ y)› ‹((τ[ev ↦ (σ y) :: τ ev][x ↦ (σ y) :: τ x]) x).head? = some (σ y)›, ‹ev ≠ x›.symm, update_swap ‹ev ≠ x›.symm]
    intros z _
    cases eq_or_ne x z <;> cases eq_or_ne z ev
    case inr.inr => simpa [‹x ≠ z›, ‹z ≠ ev›.symm] using (‹σ ∼[{x, y} ∪ ext] τ› z ‹z ∈ {x, y} ∪ ext›)
    case inl.inr => simp [‹x = z›, ‹z ≠ ev›.symm]
    all_goals (rw [‹z = ev›] at ‹z ∈ {x, y} ∪ ext›; contradiction)
  case INC.some.some x σ τ =>
    simp only [LOOP.eval, l2s, SCORE.eval]
    split
    · intros y _
      cases eq_or_ne x y <;> cases eq_or_ne y ev
      case inr.inr => simpa [‹x ≠ y›, ‹y ≠ ev›.symm] using (‹σ ∼[{x} ∪ ext] τ› y ‹y ∈ {x} ∪ ext›)
      case inl.inr => simpa [‹x = y›, ‹y ≠ ev›.symm, ←‹σ ∼[{x} ∪ ext] τ› y] using ‹((τ[ev ↦ 0 :: τ ev]) x).head? = some _›
      all_goals (rw [‹y = ev›] at ‹y ∈ {x} ∪ ext›; contradiction)
    · have ⟨_, _⟩ : ev ≠ x ∧ ev ∉ ext := by simpa using ‹ev ∉ {x} ∪ ext›
      simp [‹ev ≠ x› , ←‹σ ∼[{x} ∪ ext] τ› x] at ‹((τ[ev ↦ 0 :: τ ev]) x).head? = none›
  case SEQ.some.some Q R ih₁ ih₂ σ τ =>
    simp only [LOOP.eval, l2s, SCORE.eval]
    have : Q.ids ∪ (R.ids ∪ ext) = R.ids ∪ (Q.ids ∪ ext) := by sorry
    have : Q.ids ∪ R.ids ∪ ext = R.ids ∪ (Q.ids ∪ ext) := by sorry
    have : ev ∉ Q.ids ∪ (R.ids ∪ ext) := by simpa using ‹ev ∉ Q.ids ∪ R.ids ∪ ext›
    have : σ ∼[Q.ids ∪ (R.ids ∪ ext)] (τ[ev ↦ 0 :: τ ev]) := by
      intro y _
      cases eq_or_ne y ev
      · rw [‹y = ev›] at ‹y ∈ Q.ids ∪ (R.ids ∪ ext)›
        contradiction
      · have : σ ∼[Q.ids ∪ (R.ids ∪ ext)] τ := by simpa using ‹σ ∼[Q.ids ∪ R.ids ∪ ext] τ›
        simpa [‹y ≠ ev›.symm] using (‹σ ∼[Q.ids ∪ (R.ids ∪ ext)] τ› y ‹y ∈ Q.ids ∪ (R.ids ∪ ext)›)
    have : LOOP.eval Q σ ∼[R.ids ∪ (Q.ids ∪ ext)] SCORE.eval (l2s ev Q) (τ[ev ↦ 0 :: τ ev]) := by
      simpa [‹Q.ids ∪ (R.ids ∪ ext) = R.ids ∪ (Q.ids ∪ ext)›] using ih₁ ‹ev ∉ Q.ids ∪ (R.ids ∪ ext)› ‹σ ∼[Q.ids ∪ (R.ids ∪ ext)] (τ[ev ↦ 0 :: τ ev])›
    have : ev ∉ R.ids ∪ (Q.ids ∪ ext) := by
      simpa [‹Q.ids ∪ R.ids ∪ ext = R.ids ∪ (Q.ids ∪ ext)›] using ‹ev ∉ Q.ids ∪ R.ids ∪ ext›
    simpa [←‹Q.ids ∪ R.ids ∪ ext = R.ids ∪ (Q.ids ∪ ext)›] using ih₂ ‹ev ∉ R.ids ∪ (Q.ids ∪ ext)› ‹LOOP.eval Q σ ∼[R.ids ∪ (Q.ids ∪ ext)] SCORE.eval (l2s ev Q) (τ[ev ↦ 0 :: τ ev])›
  case LOOP.some.some x Q ih σ τ =>
    have ⟨_, ⟨_, _⟩⟩ : ev ≠ x ∧ ev ∉ Q.ids ∧ ev ∉ ext := by simpa using ‹ev ∉ {x} ∪ Q.ids ∪ ext›
    have : ((τ[ev ↦ 0 :: τ ev]) x).head? = some ↑(σ x) := by
      have : x ∈ {x} ∪ Q.ids ∪ ext := by simp
      simpa [‹ev ≠ x›] using (‹σ ∼[{x} ∪ Q.ids ∪ ext] τ› x ‹x ∈ {x} ∪ Q.ids ∪ ext›).symm
    simp only [LOOP.eval, l2s, SCORE.eval, ‹((τ[ev ↦ 0 :: τ ev]) x).head? = some ↑(σ x)›]
    induction σ x
    case zero =>
      have : σ ∼[{x} ∪ Q.ids ∪ ext] (τ[ev ↦ 0 :: τ ev]) := by
        intro y _
        cases eq_or_ne y ev
        · rw [‹y = ev›] at ‹y ∈ {x} ∪ Q.ids ∪ ext›
          contradiction
        · simpa [‹y ≠ ev›.symm] using (‹σ ∼[{x} ∪ Q.ids ∪ ext] τ› y ‹y ∈ {x} ∪ Q.ids ∪ ext›)
      simpa using ‹σ ∼[{x} ∪ Q.ids ∪ ext] (τ[ev ↦ 0 :: τ ev])›
    case succ _ ih₂ => sorry
    /- split
    · have : x ∈ {x} ∪ Q.ids ∪ ext := Finset.mem_union_left ext (Finset.mem_union_left Q.ids (Finset.mem_singleton_self x))
      simp only [←(Option.some_inj.mp (Eq.trans (‹σ ∼[{x} ∪ Q.ids ∪ ext] τ› x ‹x ∈ {x} ∪ Q.ids ∪ ext›) ‹(τ x).head? = some _›))]
      generalize some σ = s, some τ = t at ‹σ =[{x} ∪ Q.ids ∪ ext]ₛ τ›
      induction σ x generalizing s t
      case zero =>
        simpa using ‹s =[{x} ∪ Q.ids ∪ ext]ₛ t›
      case succ _ ih₂ =>
        have : {x} ∪ Q.ids ∪ ext = Q.ids ∪ ({x} ∪ ext) := by
          rw [←Finset.union_assoc, Finset.union_comm Q.ids {x}, Finset.union_assoc]
        rw [‹{x} ∪ Q.ids ∪ ext = Q.ids ∪ ({x} ∪ ext)›] at ‹s =[{x} ∪ Q.ids ∪ ext]ₛ t› ‹ev ∉ {x} ∪ Q.ids ∪ ext›
        have : LOOP.eval Q s =[{x} ∪ Q.ids ∪ ext]ₛ SCORE.eval (l2s' ev Q) t := by
          simpa [‹{x} ∪ Q.ids ∪ ext = Q.ids ∪ ({x} ∪ ext)›] using ih ‹ev ∉ Q.ids ∪ ({x} ∪ ext)› ‹s =[Q.ids ∪ ({x} ∪ ext)]ₛ t›
        exact ih₂ (LOOP.eval Q s) (SCORE.eval (l2s' ev Q) t) ‹LOOP.eval Q s =[{x} ∪ Q.ids ∪ ext]ₛ SCORE.eval (l2s' ev Q) t›
    · simp [←‹σ =[{x} ∪ Q.ids ∪ ext]ₛ τ› x] at ‹(τ x).head? = none› -/
  all_goals (simp only [eq_states_idents] at eqs)

theorem soundness {s : LOOP.State} {t : SCORE.State} {ev : Ident} (P : LOOP.Com) : ev ∉ P.ids → s =[P.ids]ₛ t → (LOOP.eval P s) =[P.ids]ₛ (SCORE.eval (l2s' ev P) t) := by
  rw [←Finset.union_empty P.ids]
  exact soundness_ext P

end Compiler
