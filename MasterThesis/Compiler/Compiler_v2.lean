/-
"A Lean-certified reversibilization of Meyer-Ritchie LOOP language".
Master thesis in computer science, University of Turin.
Authors: Andrea Delmastro
-/
import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language
import MasterThesis.Compiler.Commons

/-!
# Compiler for LOOP language, version 2
-/

namespace Compiler

open LOOP Com Store
open SCORE Com Store
open Commons

namespace v2

def l2s (ev : Ident) (P : LOOP.Com) : SCORE.Com :=
  let rec l2s' (ev : Ident) (P : LOOP.Com) : SCORE.Com :=
    match P with
    | .SKIP     => SKIP
    | .ZER x    => CON x
    | .ASN x y  => FOR y (INC ev);;
                   CON x;;
                   FOR ev (INC x);;
                   FOR x (DEC ev)
    | .INC x    => INC x
    | .SEQ P Q  => l2s' ev P;;
                   l2s' ev Q
    | .LOOP x P => FOR x (l2s' ev P)
  CON ev;; l2s' ev P

end v2

open v2 l2s

def eq_states_idents (s : LOOP.State) (t : SCORE.State) (ids : Finset Ident) : Prop :=
  match s, t with
  | some σ, some τ => ∀ (x : Ident), x ∈ ids → some ↑(σ x) = (τ x).head?
  | _     , _      => False

notation:50 s:50 " ∼[" P:50 "] " t:50 => eq_states_idents s t P

lemma eq_states_idents_no_fail {σ : LOOP.Store} {τ : SCORE.Store} {P : LOOP.Com} {Q : SCORE.Com} {ids : Finset Ident}: LOOP.eval P σ ∼[ids] SCORE.eval Q τ → (∃σ', LOOP.eval P σ = some σ') ∧ (∃τ', SCORE.eval Q τ = some τ') := by
  intros
  cases Option.eq_none_or_eq_some (LOOP.eval P σ) <;> cases Option.eq_none_or_eq_some (SCORE.eval Q τ)
  case inr.inr =>
    constructor
    repeat assumption
  case inr.inl eq₁ eq₂ | inl.inr eq₁ eq₂ | inl.inl eq₁ eq₂ =>
    simp [eq₁, eq₂, eq_states_idents] at ‹LOOP.eval P σ ∼[ids] SCORE.eval Q τ›

lemma eq_states_idents_update {σ : LOOP.Store} {τ : SCORE.Store} {ids : Finset Ident} (x : Ident) (v : ℕ) : σ ∼[ids] τ → σ[x ↦ v] ∼[ids] τ[x ↦ ↑v :: τ x] := by
  intros _ y _
  cases eq_or_ne x y
  · simp [‹x = y›]
  · simpa [‹x ≠ y›] using ‹σ ∼[ids] τ› y ‹y ∈ ids›

lemma eq_states_idents_update_right {σ : LOOP.Store} {τ : SCORE.Store} {ids : Finset Ident} {x : Ident} {l : List Int} : σ ∼[ids] τ → x ∉ ids → σ ∼[ids] τ[x ↦ l] := by
  intros _ _ y _
  cases eq_or_ne y x
  · rw [‹y = x›] at ‹y ∈ ids›
    contradiction
  · simpa [‹y ≠ x›.symm] using ‹σ ∼[ids] τ› y ‹y ∈ ids›

namespace v2

lemma ev_invariant {τ τ' : SCORE.Store} {ev : Ident} {P : LOOP.Com} (h_ids : ev ∉ P.ids) : (τ ev).head? = some 0 → SCORE.eval (l2s' ev P) τ = τ' → (τ' ev).head? = some 0 := by
  sorry

lemma ev_inariant_ASN {τ τ' : SCORE.Store} {x y ev : Ident} (h_ids : ev ∉ (ASN x y).ids) : (τ ev).head? = some 0 → SCORE.eval (l2s' ev (ASN x y)) τ = τ' → (τ' ev).head? = some 0 := by
  intros h_ev eqs_eval
  rw [LOOP.Com.ids] at *
  have ⟨_, _⟩ : ev ≠ x ∧ ev ≠ y := by simpa using h_ids
  have ⟨v, _⟩ : ∃(v : Int), (τ y).head? = v := by
    simp only [l2s', SCORE.eval] at ‹SCORE.eval (l2s' ev (ASN x y)) τ = τ'›
    split at eqs_eval
    case h_1 v _ => exact ⟨v, ‹(τ y).head? = v›⟩
    case h_2 => simp only [SCORE.eval] at eqs_eval
  have : eval (l2s' ev (ASN x y)) τ = τ[x ↦ v :: τ x][ev ↦ 0 :: (τ ev).tail] := by
    calc
      eval (l2s' ev (ASN x y)) τ
      _ = eval (FOR y (INC ev);; CON x;; FOR ev (INC x);; FOR x (DEC ev)) τ := by
            simp [l2s']
      _ = eval (CON x;; FOR ev (INC x);; FOR x (DEC ev)) (eval (FOR y (INC ev)) τ) := by
            simp [SCORE.eval]
      _ = eval (CON x;; FOR ev (INC x);; FOR x (DEC ev)) (τ[ev ↦ v :: (τ ev).tail]) := by
            simp [for_inc ‹(τ ev).head? = some 0› ‹(τ y).head? = v ›]
      _ = eval (FOR ev (INC x);; FOR x (DEC ev)) (τ[ev ↦ v :: (τ ev).tail][x ↦ 0 :: τ x]) := by
            simp[SCORE.eval, ‹ev ≠ x›]
      _ = eval (FOR x (DEC ev)) (eval (FOR ev (INC x)) (τ[ev ↦ v :: (τ ev).tail][x ↦ 0 :: τ x])) := by
            simp [SCORE.eval]
      _ = eval (FOR x (DEC ev)) (τ[ev ↦ v :: (τ ev).tail][x ↦ v :: τ x]) := by
            have : ((τ[ev ↦ v :: (τ ev).tail][x ↦ 0 :: τ x]) x).head? = some 0 := by simp
            have : ((τ[ev ↦ v :: (τ ev).tail][x ↦ 0 :: τ x]) ev).head? = v := by simp [‹ev ≠ x›.symm]
            simp [for_inc ‹((τ[ev ↦ v :: (τ ev).tail][x ↦ 0 :: τ x]) x).head? = some 0›
                    ‹((τ[ev ↦ v :: (τ ev).tail][x ↦ 0 :: τ x]) ev).head? = v›]
      _ = τ[x ↦ v :: τ x][ev ↦ 0 :: (τ ev).tail] := by
            have : ((τ[ev ↦ v :: (τ ev).tail][x ↦ v :: τ x]) ev).head? = v := by simp [‹ev ≠ x›.symm]
            have : ((τ[ev ↦ v :: (τ ev).tail][x ↦ v :: τ x]) x).head? = v := by simp
            simp [for_dec ‹((τ[ev ↦ v :: (τ ev).tail][x ↦ v :: τ x]) ev).head? = v›
                    ‹((τ[ev ↦ v :: (τ ev).tail][x ↦ v :: τ x]) x).head? = v›,
                  ‹ev ≠ x›.symm, update_swap ‹ev ≠ x›.symm]
  have : τ' =  τ[x ↦ v :: τ x][ev ↦ 0 :: (τ ev).tail] := by
    simpa [‹eval (l2s' ev (ASN x y)) τ = τ[x ↦ v :: τ x][ev ↦ 0 :: (τ ev).tail]›]
      using ‹SCORE.eval (l2s' ev (ASN x y)) τ =  τ'›.symm
  simp [‹τ' =  τ[x ↦ v :: τ x][ev ↦ 0 :: (τ ev).tail]›]

lemma soundness'_ext {σ : LOOP.Store} {τ : SCORE.Store} {ev : Ident} {ext : Finset Ident} (P : LOOP.Com) : ev ∉ (P.ids ∪ ext) → (τ ev).head? = some 0 → σ ∼[P.ids ∪ ext] τ → (LOOP.eval P σ) ∼[P.ids ∪ ext] (SCORE.eval (l2s' ev P) τ) := by
  intros h_head_ev h_ev eqs
  induction P generalizing σ τ ext <;> rw [LOOP.Com.ids] at *
  case SKIP =>
     simpa only [LOOP.eval, l2s', SCORE.eval]
  case ZER x =>
    simp only [LOOP.eval, l2s', SCORE.eval]
    exact eq_states_idents_update x 0 ‹σ ∼[{x} ∪ ext] τ›
  case ASN x y =>
    have ⟨_, ⟨_, _⟩⟩ : ev ≠ x ∧ ev ≠ y ∧ ev ∉ ext := by simpa using ‹ev ∉ {x, y} ∪ ext›
    have : (τ y).head? = some (σ y) := by
      have : y ∈ {x, y} ∪ ext := by simp
      simpa [‹ev ≠ y›] using (‹σ ∼[{x, y} ∪ ext] τ› y ‹y ∈ {x, y} ∪ ext›).symm
    simp only [LOOP.eval, l2s']
    calc
      eval (FOR y (INC ev);; CON x;; FOR ev (INC x);; FOR x (DEC ev)) τ
      _ = eval (CON x;; FOR ev (INC x);; FOR x (DEC ev)) (eval (FOR y (INC ev)) τ) := by
            simp [SCORE.eval]
      _ = eval (CON x;; FOR ev (INC x);; FOR x (DEC ev)) (τ[ev ↦ (σ y) :: (τ ev).tail]) := by
            simp [for_inc ‹(τ ev).head? = some 0› ‹(τ y).head? = some (σ y)›]
      _ = eval (FOR ev (INC x);; FOR x (DEC ev)) (τ[ev ↦ (σ y) :: (τ ev).tail][x ↦ 0 :: τ x]) := by
            simp[SCORE.eval, ‹ev ≠ x›]
      _ = eval (FOR x (DEC ev)) (eval (FOR ev (INC x)) (τ[ev ↦ (σ y) :: (τ ev).tail][x ↦ 0 :: τ x])) := by
            simp [SCORE.eval]
      _ = eval (FOR x (DEC ev)) (τ[ev ↦ (σ y) :: (τ ev).tail][x ↦ (σ y) :: τ x]) := by
            have : ((τ[ev ↦ (σ y) :: (τ ev).tail][x ↦ 0 :: τ x]) x).head? = some 0 := by simp
            have : ((τ[ev ↦ (σ y) :: (τ ev).tail][x ↦ 0 :: τ x]) ev).head? = some (σ y) := by simp [‹ev ≠ x›.symm]
            simp [for_inc ‹((τ[ev ↦ (σ y) :: (τ ev).tail][x ↦ 0 :: τ x]) x).head? = some 0›
                    ‹((τ[ev ↦ (σ y) :: (τ ev).tail][x ↦ 0 :: τ x]) ev).head? = some (σ y)›]
      _ = τ[x ↦ (σ y) :: τ x][ev ↦ 0 :: (τ ev).tail] := by
            have : ((τ[ev ↦ (σ y) :: (τ ev).tail][x ↦ (σ y) :: τ x]) ev).head? = some (σ y) := by simp [‹ev ≠ x›.symm]
            have : ((τ[ev ↦ (σ y) :: (τ ev).tail][x ↦ (σ y) :: τ x]) x).head? = some (σ y) := by simp
            simp [for_dec ‹((τ[ev ↦ (σ y) :: (τ ev).tail][x ↦ (σ y) :: τ x]) ev).head? = some (σ y)›
                    ‹((τ[ev ↦ (σ y) :: (τ ev).tail][x ↦ (σ y) :: τ x]) x).head? = some (σ y)›,
                  ‹ev ≠ x›.symm, update_swap ‹ev ≠ x›.symm]
    intros z _
    cases eq_or_ne x z <;> cases eq_or_ne z ev
    case inr.inr => simpa [‹x ≠ z›, ‹z ≠ ev›.symm] using (‹σ ∼[{x, y} ∪ ext] τ› z ‹z ∈ {x, y} ∪ ext›)
    case inl.inr => simp [‹x = z›, ‹z ≠ ev›.symm]
    all_goals (rw [‹z = ev›] at ‹z ∈ {x, y} ∪ ext›; contradiction)
  case INC x =>
    have ⟨_, _⟩ : ev ≠ x ∧ ev ∉ ext := by simpa using ‹ev ∉ {x} ∪ ext›
    have : (τ x).head? = some ↑(σ x) := by
      have : x ∈ {x} ∪ ext := by simp
      simpa [‹ev ≠ x›] using (‹σ ∼[{x} ∪ ext] τ› x ‹x ∈ {x} ∪ ext›).symm
    simp only [LOOP.eval, l2s', SCORE.eval, ‹(τ x).head? = some ↑(σ x)›]
    intros y _
    cases eq_or_ne x y
    · simp [‹x = y›]
    · simpa [‹x ≠ y›] using ‹σ ∼[{x} ∪ ext] τ› y ‹y ∈ {x} ∪ ext›
  case SEQ Q R ih₁ ih₂ =>
    have ⟨_, ⟨_, _⟩⟩ : ev ∉ Q.ids ∧ ev ∉ R.ids ∧ ev ∉ ext := by simpa using ‹ev ∉ Q.ids ∪ R.ids ∪ ext›
    simp only [LOOP.eval, l2s', SCORE.eval]
    have : LOOP.eval Q σ ∼[R.ids ∪ (Q.ids ∪ ext)] SCORE.eval (l2s' ev Q) τ := by
      have : Q.ids ∪ (R.ids ∪ ext) = R.ids ∪ (Q.ids ∪ ext) :=
        calc
          Q.ids ∪ (R.ids ∪ ext)
          _ = (Q.ids ∪ R.ids) ∪ ext := by simp [Finset.union_assoc]
          _ = (R.ids ∪ Q.ids) ∪ ext := by simp [Finset.union_comm]
          _ = R.ids ∪ (Q.ids ∪ ext) := by simp [Finset.union_assoc]
      have : σ ∼[Q.ids ∪ (R.ids ∪ ext)] τ := by
        simpa [‹Q.ids ∪ (R.ids ∪ ext) = R.ids ∪ (Q.ids ∪ ext)›]
          using ‹σ ∼[Q.ids ∪ R.ids ∪ ext] τ›
      have : ev ∉ Q.ids ∪ (R.ids ∪ ext) := by
        simpa using ‹ev ∉ Q.ids ∪ R.ids ∪ ext›
      simpa [‹Q.ids ∪ (R.ids ∪ ext) = R.ids ∪ (Q.ids ∪ ext)›]
        using ih₁ ‹ev ∉ Q.ids ∪ (R.ids ∪ ext)› ‹(τ ev).head? = some 0› ‹σ ∼[Q.ids ∪ (R.ids ∪ ext)] τ›
    have ⟨⟨σ', _⟩, ⟨τ', _⟩⟩ : (∃σ', (LOOP.eval Q σ) = some σ') ∧ (∃τ', (SCORE.eval (l2s' ev Q) τ) = some τ') :=
        eq_states_idents_no_fail ‹LOOP.eval Q σ ∼[R.ids ∪ (Q.ids ∪ ext)] SCORE.eval (l2s' ev Q) τ›
    have : Q.ids ∪ R.ids ∪ ext = R.ids ∪ (Q.ids ∪ ext) :=
      calc
          Q.ids ∪ R.ids ∪ ext
          _ = R.ids ∪ Q.ids ∪ ext := by simp [Finset.union_comm]
          _ = R.ids ∪ (Q.ids ∪ ext) := by simp [Finset.union_assoc]
    have : σ' ∼[R.ids ∪ (Q.ids ∪ ext)] τ' := by
      simpa [‹LOOP.eval Q σ = σ'›, ‹SCORE.eval (l2s' ev Q) τ = τ'›]
        using ‹LOOP.eval Q σ ∼[R.ids ∪ (Q.ids ∪ ext)] SCORE.eval (l2s' ev Q) τ›
    have : (τ' ev).head? = some 0 :=
      ev_invariant ‹ev ∉ Q.ids› ‹(τ ev).head? = some 0› ‹SCORE.eval (l2s' ev Q) τ = τ'›
    have : ev ∉ R.ids ∪ (Q.ids ∪ ext) := by
      simpa [‹Q.ids ∪ R.ids ∪ ext = R.ids ∪ (Q.ids ∪ ext)›] using ‹ev ∉ Q.ids ∪ R.ids ∪ ext›
    simpa [←‹Q.ids ∪ R.ids ∪ ext = R.ids ∪ (Q.ids ∪ ext)›, ←‹SCORE.eval (l2s' ev Q) τ = τ'›, ←‹LOOP.eval Q σ = σ'›]
      using ih₂ ‹ev ∉ R.ids ∪ (Q.ids ∪ ext)› ‹(τ' ev).head? = some 0› ‹σ' ∼[R.ids ∪ (Q.ids ∪ ext)] τ'›
  case LOOP x Q ih =>
    have ⟨_, ⟨_, _⟩⟩ : ev ≠ x ∧ ev ∉ Q.ids ∧ ev ∉ ext := by simpa using ‹ev ∉ {x} ∪ Q.ids ∪ ext›
    have : (τ x).head? = some ↑(σ x) := by
      have : x ∈ {x} ∪ Q.ids ∪ ext := by simp
      simpa [‹ev ≠ x›] using (‹σ ∼[{x} ∪ Q.ids ∪ ext] τ› x ‹x ∈ {x} ∪ Q.ids ∪ ext›).symm
    simp only [LOOP.eval, l2s', SCORE.eval, ‹(τ x).head? = some ↑(σ x)›]
    clear ‹(τ x).head? = some ↑(σ x)›
    induction σ x generalizing σ τ
    case zero =>
      simpa using ‹σ ∼[{x} ∪ Q.ids ∪ ext] τ›
    case succ m ih₂ =>
      have : {x} ∪ Q.ids ∪ ext = Q.ids ∪ ({x} ∪ ext) :=
        calc
          {x} ∪ Q.ids ∪ ext
          _ = Q.ids ∪ {x} ∪ ext := by simp [Finset.union_comm]
          _ = Q.ids ∪ ({x} ∪ ext) := by simp [Finset.union_assoc]
      have : LOOP.eval Q σ ∼[Q.ids ∪ ({x} ∪ ext)] SCORE.eval (l2s' ev Q) τ := by
        have : σ ∼[Q.ids ∪ ({x} ∪ ext)] τ := by
          simpa [‹{x} ∪ Q.ids ∪ ext = Q.ids ∪ ({x} ∪ ext)›]
            using ‹σ ∼[{x} ∪ Q.ids ∪ ext] τ›
        have : ev ∉ Q.ids ∪ ({x} ∪ ext) := by
          simpa [‹{x} ∪ Q.ids ∪ ext = Q.ids ∪ ({x} ∪ ext)›]
            using ‹ev ∉ {x} ∪ Q.ids ∪ ext›
        exact ih ‹ev ∉ Q.ids ∪ ({x} ∪ ext)›
          ‹(τ ev).head? = some 0›
          ‹σ ∼[Q.ids ∪ ({x} ∪ ext)] τ›
      have ⟨⟨σ', _⟩, ⟨τ', _⟩⟩ : (∃σ', (LOOP.eval Q σ) = some σ') ∧ (∃τ', (SCORE.eval (l2s' ev Q) τ) = some τ') :=
        eq_states_idents_no_fail ‹LOOP.eval Q σ ∼[Q.ids ∪ ({x} ∪ ext)] SCORE.eval (l2s' ev Q) τ›
      have : σ' ∼[{x} ∪ Q.ids ∪ ext] τ' := by
        simpa [‹SCORE.eval (l2s' ev Q) τ = τ'›, ‹LOOP.eval Q σ = σ'›, ←‹{x} ∪ Q.ids ∪ ext = Q.ids ∪ ({x} ∪ ext)›]
          using ‹LOOP.eval Q σ ∼[Q.ids ∪ ({x} ∪ ext)] SCORE.eval (l2s' ev Q) τ›
      simpa [←‹SCORE.eval (l2s' ev Q) τ = τ'›, ←‹LOOP.eval Q σ = σ'›]
        using ih₂ (ev_invariant ‹ev ∉ Q.ids› ‹(τ ev).head? = some 0› ‹SCORE.eval (l2s' ev Q) τ = τ'›)
          ‹σ' ∼[{x} ∪ Q.ids ∪ ext] τ'›

lemma soundness_ext {s : LOOP.State} {t : SCORE.State} {ev : Ident} {ext : Finset Ident} (P : LOOP.Com) : ev ∉ (P.ids ∪ ext) → s ∼[P.ids ∪ ext] t → (LOOP.eval P s) ∼[P.ids ∪ ext] (SCORE.eval (l2s ev P) t) := by
  intros h_ev eqs
  cases s <;> cases t
  case some.some σ τ =>
    simp only [l2s, SCORE.eval]
    have : ((τ[ev ↦ 0 :: τ ev]) ev).head? = some 0 := by simp
    exact soundness'_ext P ‹ev ∉ P.ids ∪ ext›
      ‹((τ[ev ↦ 0 :: τ ev]) ev).head? = some 0›
      (eq_states_idents_update_right ‹σ ∼[P.ids ∪ ext] τ› ‹ev ∉ P.ids ∪ ext›)
  all_goals (simp only [eq_states_idents] at eqs)

theorem soundness {s : LOOP.State} {t : SCORE.State} {ev : Ident} (P : LOOP.Com) : ev ∉ P.ids → s ∼[P.ids] t → (LOOP.eval P s) ∼[P.ids] (SCORE.eval (l2s ev P) t) := by
  simpa using @soundness_ext s t ev ∅ P

end v2

end Compiler
