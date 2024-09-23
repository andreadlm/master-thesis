import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith
import MasterThesis.LOOP.Language
import MasterThesis.SCORE.Language
import MasterThesis.Compiler.Compiler_v2

namespace l2s'

open SCORE Com
open LOOP Com

lemma iter_inc {x : Ident} {σ : SCORE.Store} {k : Int} (v : ℕ) : (σ x).head? = k → (fun t ↦ SCORE.eval (INC x) t)^[v] σ = σ[x ↦ (k + ↑v) :: (σ x).tail] := by
  intro
  induction v
  case zero =>
    simp [Store.update_unchanged_cons ‹(σ x).head? = k›]
  case succ m ih =>
    calc
      (fun t => SCORE.eval (INC x) t)^[m + 1] σ
      _ = eval (INC x) ((fun t => SCORE.eval (INC x) t)^[m] σ) := by simp [Nat.add_comm m 1, Function.iterate_add_apply]
      _ = eval (INC x) (σ[x ↦ (k + ↑m) :: (σ x).tail])         := by rw [ih]
      _ = σ[x ↦ (k + ↑m + 1) :: (σ x).tail]                    := by simp [SCORE.eval, ‹(σ x).head? = k›]
      _ = σ[x ↦ (k + ↑(m + 1)) :: (σ x).tail]                  := by
        have : k + ↑m + 1 = k + (↑m + 1) := by linarith
        simp [this]

lemma iter_dec {x : Ident} {σ : SCORE.Store} {k : Int} (v : ℕ) : (σ x).head? = k → (fun t ↦ SCORE.eval (DEC x) t)^[v] σ = σ[x ↦ (k - ↑v) :: (σ x).tail] := by
  intro
  induction v
  case zero =>
    simp [Store.update_unchanged_cons ‹(σ x).head? = k›]
  case succ m ih =>
    calc
      (fun t => SCORE.eval (DEC x) t)^[m + 1] σ
      _ = eval (DEC x) ((fun t => SCORE.eval (DEC x) t)^[m] σ) := by simp [Nat.add_comm m 1, Function.iterate_add_apply]
      _ = eval (DEC x) (σ[x ↦ (k - ↑m) :: (σ x).tail])         := by rw [ih]
      _ = σ[x ↦ (k - ↑m - 1) :: (σ x).tail]                    := by simp [SCORE.eval, ‹(σ x).head? = k›]
      _ = σ[x ↦ (k - ↑(m + 1)) :: (σ x).tail]                  := by
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
        _ = σ[x ↦ (v₁ + ↑k) :: (σ x).tail] := iter_inc k ‹(σ x).head? = v₁›
        _ = σ[x ↦ (v₁ + v₂) :: (σ x).tail] := by simp [Option.some.inj (Eq.trans ‹(σ y).head? = v₂›.symm ‹(σ y).head? = Int.ofNat k›)]
    case _ k _ =>
      have evalI_INC_eq_eval_DEC {x : Ident} {s : SCORE.State} : evalI (INC x) s = eval (DEC x) s := by
        cases Option.eq_none_or_eq_some s
        · rw [‹s = none›, SCORE.evalI, SCORE.eval]
        · cases ‹∃ x, s = some x› with
          | intro σ _ => rw [‹s = σ›, SCORE.evalI, SCORE.eval]
      calc
        (fun t => SCORE.evalI (INC x) t)^[k + 1] σ
        _ = (fun t => SCORE.eval (DEC x) t)^[k + 1] σ := by simp only [evalI_INC_eq_eval_DEC]
        _ = σ[x ↦ (v₁ - ↑(k + 1)) :: (σ x).tail]      := iter_dec (k + 1) ‹(σ x).head? = v₁›
        _ = σ[x ↦ (v₁ + v₂) :: (σ x).tail]            := by simp [Int.sub_eq_add_neg, Int.negSucc_eq k,
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
        (fun t => SCORE.eval (DEC x) t)^[k] σ
        _ = σ[x ↦ (v₁ - ↑k) :: (σ x).tail] := iter_dec k ‹(σ x).head? = v₁›
        _ = σ[x ↦ (v₁ - v₂) :: (σ x).tail] := by simp [Option.some.inj (Eq.trans ‹(σ y).head? = v₂›.symm ‹(σ y).head? = Int.ofNat k›)]
    case _ k _ =>
      have evalI_DEC_eq_eval_INC {x : Ident} {s : SCORE.State} : evalI (DEC x) s = eval (INC x) s := by
        cases Option.eq_none_or_eq_some s
        · rw [‹s = none›, SCORE.evalI, SCORE.eval]
        · cases ‹∃ x, s = some x› with
          | intro σ _ => rw [‹s = σ›, SCORE.evalI, SCORE.eval]
      calc
        (fun t => SCORE.evalI (DEC x) t)^[k + 1] σ
        _ = (fun t => SCORE.eval (INC x) t)^[k + 1] σ := by simp only [evalI_DEC_eq_eval_INC]
        _ = σ[x ↦ (v₁ + ↑(k + 1)) :: (σ x).tail]      := iter_inc (k + 1) ‹(σ x).head? = v₁›
        _ = σ[x ↦ (v₁ - v₂) :: (σ x).tail]            := by simp [Int.sub_eq_add_neg, Int.negSucc_eq k,
                                                                  Option.some.inj (Eq.trans ‹(σ y).head? = v₂›.symm ‹(σ y).head? = Int.negSucc k›)]
  · rw [‹(σ y).head? = v₂›] at ‹(σ y).head? = none›
    contradiction

lemma ev_invariant {x y ev : Ident} {v₁ v₂ : Int} {σ : SCORE.Store} (h : ev ∉ (ASN x y).ids) : (σ x).head? = v₁ → (σ y).head? = v₂ → ∃ (σ' : SCORE.Store), (eval (l2s' ev (ASN x y)) σ = σ' ∧ (σ' ev).head? = some 0) := by
  intros
  have : x ≠ ev := sorry
  have : y ≠ ev := sorry
  repeat constructor
  repeat sorry
  /-
  · rw [l2s']
    /- calc
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
        simp [SCORE.eval, for_dec head_ev head_x, ‹x ≠ ev› -/
  · simp
  -/

theorem soundness_ext {s : LOOP.State} {t : SCORE.State} {ev : Ident} {ext : Finset Ident} (P : LOOP.Com) : ev ∉ (P.ids ∪ ext) → s =[P.ids ∪ ext]ₛ t → (LOOP.eval P s) =[P.ids ∪ ext]ₛ (SCORE.eval (l2s' ev P) t) := by
  intros h_ev eqs
  induction P generalizing s t ext
  all_goals (cases s <;> cases t <;> rw [LOOP.Com.ids] at *)
  case SKIP.some.some σ τ =>
    simp only [LOOP.eval, l2s', SCORE.eval]
    intros y _
    cases eq_or_ne y ev
    · rw [‹y = ev›] at ‹y ∈ ∅ ∪ ext›
      contradiction
    · simpa [‹y ≠ ev›.symm] using (‹σ =[∅ ∪ ext]ₛ τ› y ‹y ∈ ∅ ∪ ext›)
  case ZER.some.some x σ τ =>
    simp only [LOOP.eval, l2s', SCORE.eval]
    intros y _
    cases eq_or_ne x y <;> cases eq_or_ne y ev
    case inr.inr => simpa [‹x ≠ y›, ‹y ≠ ev›.symm] using (‹σ =[{x} ∪ ext]ₛ τ› y ‹y ∈ {x} ∪ ext›)
    case inr.inl => rw [‹y = ev›] at ‹y ∈ {x} ∪ ext›
                    contradiction
    all_goals simp [‹x = y›]
  case ASN.some.some x y σ τ =>
    sorry
  case INC.some.some x σ τ =>
    simp only [LOOP.eval, l2s', SCORE.eval]
    have : ev ≠ x := by sorry
    split
    · intros y _
      cases eq_or_ne x y <;> cases eq_or_ne y ev
      case inr.inr => simpa [‹x ≠ y›, ‹y ≠ ev›.symm] using (‹σ =[{x} ∪ ext]ₛ τ› y ‹y ∈ {x} ∪ ext›)
      case inl.inr => simpa [‹x = y›, ‹y ≠ ev›.symm, ←‹σ =[{x} ∪ ext]ₛ τ› y] using ‹((τ[ev ↦ 0 :: τ ev]) x).head? = some _›
      all_goals (rw [‹y = ev›] at ‹y ∈ {x} ∪ ext›; contradiction)
    · simp [‹ev ≠ x› , ←‹σ =[{x} ∪ ext]ₛ τ› x] at ‹((τ[ev ↦ 0 :: τ ev]) x).head? = none›
  case SEQ.some.some LQ LR ih₁ ih₂ σ τ =>
    have : LQ.ids ∪ LR.ids ∪ ext = LQ.ids ∪ (LR.ids ∪ ext) := by rw [Finset.union_assoc]
    have : LQ.ids ∪ LR.ids ∪ ext = LR.ids ∪ (LQ.ids ∪ ext) := by rw [Finset.union_comm LQ.ids LR.ids, Finset.union_assoc]
    have : LQ.ids ∪ (LR.ids ∪ ext) = LR.ids ∪ (LQ.ids ∪ ext) := by rw [←Finset.union_assoc, Finset.union_comm LQ.ids LR.ids, Finset.union_assoc]
    rw [LOOP.eval, l2s', SCORE.eval, ‹LQ.ids ∪ LR.ids ∪ ext = LR.ids ∪ (LQ.ids ∪ ext)›]
    have : ev ∉ LQ.ids ∪ (LR.ids ∪ ext) := by
      simpa [‹LQ.ids ∪ LR.ids ∪ ext = LQ.ids ∪ (LR.ids ∪ ext)›] using ‹ev ∉ LQ.ids ∪ LR.ids ∪ ext›
    have : σ =[LQ.ids ∪ (LR.ids ∪ ext)]ₛ τ := by
      simpa [‹LQ.ids ∪ LR.ids ∪ ext = LQ.ids ∪ (LR.ids ∪ ext)›] using ‹σ =[LQ.ids ∪ LR.ids ∪ ext]ₛ τ›
    have : (LOOP.eval LQ (some σ)) =[LR.ids ∪ (LQ.ids ∪ ext)]ₛ (SCORE.eval (l2s' ev LQ) (some τ)) := by
      simpa [‹LQ.ids ∪ (LR.ids ∪ ext) = LR.ids ∪ (LQ.ids ∪ ext)›] using ih₁ ‹ev ∉ LQ.ids ∪ (LR.ids ∪ ext)› ‹σ =[LQ.ids ∪ (LR.ids ∪ ext)]ₛ τ›
    have : ev ∉ LR.ids ∪ (LQ.ids ∪ ext) := by
      simpa [‹LQ.ids ∪ LR.ids ∪ ext = LR.ids ∪ (LQ.ids ∪ ext)›] using ‹ev ∉ LQ.ids ∪ LR.ids ∪ ext›
    exact ih₂ ‹ev ∉ LR.ids ∪ (LQ.ids ∪ ext)› ‹(LOOP.eval LQ (some σ)) =[LR.ids ∪ (LQ.ids ∪ ext)]ₛ (SCORE.eval (l2s' ev LQ) (some τ))›
  case LOOP.some.some x LQ ih σ τ =>
    rw [LOOP.eval, l2s', SCORE.eval]
    split
    · have : x ∈ {x} ∪ LQ.ids ∪ ext := Finset.mem_union_left ext (Finset.mem_union_left LQ.ids (Finset.mem_singleton_self x))
      simp only [←(Option.some_inj.mp (Eq.trans (‹σ =[{x} ∪ LQ.ids ∪ ext]ₛ τ› x ‹x ∈ {x} ∪ LQ.ids ∪ ext›) ‹(τ x).head? = some _›))]
      generalize some σ = s, some τ = t at ‹σ =[{x} ∪ LQ.ids ∪ ext]ₛ τ›
      induction σ x generalizing s t
      case zero =>
        simpa using ‹s =[{x} ∪ LQ.ids ∪ ext]ₛ t›
      case succ _ ih₂ =>
        have : {x} ∪ LQ.ids ∪ ext = LQ.ids ∪ ({x} ∪ ext) := by
          rw [←Finset.union_assoc, Finset.union_comm LQ.ids {x}, Finset.union_assoc]
        rw [‹{x} ∪ LQ.ids ∪ ext = LQ.ids ∪ ({x} ∪ ext)›] at ‹s =[{x} ∪ LQ.ids ∪ ext]ₛ t› ‹ev ∉ {x} ∪ LQ.ids ∪ ext›
        have : LOOP.eval LQ s =[{x} ∪ LQ.ids ∪ ext]ₛ SCORE.eval (l2s' ev LQ) t := by
          simpa [‹{x} ∪ LQ.ids ∪ ext = LQ.ids ∪ ({x} ∪ ext)›] using ih ‹ev ∉ LQ.ids ∪ ({x} ∪ ext)› ‹s =[LQ.ids ∪ ({x} ∪ ext)]ₛ t›
        exact ih₂ (LOOP.eval LQ s) (SCORE.eval (l2s' ev LQ) t) ‹LOOP.eval LQ s =[{x} ∪ LQ.ids ∪ ext]ₛ SCORE.eval (l2s' ev LQ) t›
    · simp [←‹σ =[{x} ∪ LQ.ids ∪ ext]ₛ τ› x] at ‹(τ x).head? = none›
  all_goals (simp only [eq_states_idents] at eqs)

theorem soundness {s : LOOP.State} {t : SCORE.State} {ev : Ident} (P : LOOP.Com) : ev ∉ P.ids → s =[P.ids]ₛ t → (LOOP.eval P s) =[P.ids]ₛ (SCORE.eval (l2s' ev P) t) := by
  rw [←Finset.union_empty P.ids]
  exact soundness_ext P
