/-
"A Lean-certified reversibilization of Meyer-Ritchie LOOP language".
Master thesis in computer science, University of Turin.
Authors: Andrea Delmastro
-/
import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language
import MasterThesis.Compiler.Commons

/-!
# Compiler for LOOP language, version 1

This file defines a compiler that translates (_reversibilizes_) any LOOP program into a corresponding
SCORE program based on a specific notion of equivalence between LOOP states and SCORE states.

## Notations

* `s ∼ t` stands for `eq_states s t` (`s` _and_ `t` _are equivalent_).
-/

namespace Compiler

open LOOP Com
open SCORE Com
open Commons

namespace v1

/-- Syntax-directed compiler from LOOP programs to SCORE programs. The compiler takes as input a
`LOOP.Com` and outputs the equivalent `SCORE.Com`.
-/
def l2s (P : LOOP.Com) : SCORE.Com :=
  match P with
  | .SKIP     => SKIP
  | .ZER x    => CON x
  | .ASN x y  => if x ≠ y then
                   CON x;;
                   FOR y (INC x)
                 else SKIP
  | .INC x    => INC x
  | .SEQ P Q  => l2s P;;
                 l2s Q
  | .LOOP x P => FOR x (l2s P)

end v1

/-- Notion of equivalence between LOOP states and SCORE states. A LOOP state `s` is said to be
equivalent to a SCORE state `t` if for each identifier `x` the value of the register identified
by `x` in `s` is equal to the current value of the variable identified by `x` in `t`. -/
def eq_states (s : LOOP.State) (t : SCORE.State) : Prop :=
  match s, t with
  | some σ, some τ => ∀ (x : Ident), some ↑(σ x) = (τ x).head?
  | _     , _      => False

infix:50 "∼" => eq_states

/-- Two states are kept equivalent if the first is updated by assigning a new value `v` to the
register identified by `x` and the second is updated by inserting `v` on top of the stack identified
by `x`. -/
lemma eq_states_update {σ : LOOP.Store} {τ : SCORE.Store} (x : Ident) (v : ℕ) : σ ∼ τ → σ[x ↦ v] ∼ τ[x ↦ ↑v :: τ x] := by
  intros _ y
  cases eq_or_ne x y
  · simp [‹x = y›]
  · simpa [‹x ≠ y›] using ‹σ ∼ τ› y

namespace v1

/-- Let `P` be a LOOP program, `σ` a LOOP state and `τ` a SCORE state. If the two states are equivalent,
then the evaluation of `P` in `σ` and the compiled SCORE program `l2s P` in `τ` end in two equivalent
states. -/
theorem soundness {s : LOOP.State} {t : SCORE.State} (P : LOOP.Com) : s ∼ t → (LOOP.eval P s) ∼ (SCORE.eval (l2s P) t) := by
  intro eqs
  induction P generalizing s t
  all_goals (cases s <;> cases t)
  case SKIP.some.some σ τ =>
    rwa [LOOP.eval, l2s, SCORE.eval]
  case ZER.some.some x σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    exact eq_states_update x 0 ‹σ ∼ τ›
  case ASN.some.some x y σ τ =>
    rw [LOOP.eval]
    cases eq_or_ne x y
    · simpa [l2s, ‹x = y›, SCORE.eval]
    · have : SCORE.eval (l2s (ASN x y)) τ = τ[x ↦ (σ y) :: τ x] := by
        calc
          SCORE.eval (l2s (ASN x y)) τ
          _ = SCORE.eval (FOR y (INC x)) (τ[x ↦ 0 :: τ x]) :=
                by simp [l2s, ‹x ≠ y›, SCORE.eval]
          _ = τ[x ↦ (σ y) :: τ x] := by
                have : ((τ[x ↦ 0 :: τ x]) x).head? = some 0 := by simp
                have : ((τ[x ↦ 0 :: τ x]) y).head? = some (σ y) := by simpa [‹x ≠ y›] using (‹σ ∼ τ› y).symm
                simpa using for_inc ‹((τ[x ↦ 0 :: τ x]) x).head? = some 0›
                                    ‹((τ[x ↦ 0 :: τ x]) y).head? = some (σ y)›
      simpa [‹SCORE.eval (l2s (ASN x y)) τ = τ[x ↦ (σ y) :: τ x]›]
        using  eq_states_update x (σ y) ‹σ ∼ τ›
  case INC.some.some x σ τ =>
    simp [LOOP.eval, l2s, SCORE.eval, (‹σ ∼ τ› x).symm]
    intro y
    cases eq_or_ne x y
    · simp [‹x = y›]
    · simpa [‹x ≠ y›] using ‹σ ∼ τ› y
  case SEQ.some.some Q R ih₁ ih₂ σ τ =>
    rw [LOOP.eval, l2s, SCORE.eval]
    exact ih₂ (ih₁ ‹σ ∼ τ›)
  case LOOP.some.some x Q ih σ τ =>
    simp [LOOP.eval, l2s, SCORE.eval, ←(‹σ ∼ τ› x)]
    generalize some σ = s, some τ = t at ‹σ ∼ τ›
    induction σ x generalizing s t
    case zero =>
      simpa
    case succ _ ih₂ =>
      exact ih₂ (LOOP.eval Q s) (SCORE.eval (l2s Q) t) (ih ‹s ∼ t›)
  all_goals (simp only [eq_states] at eqs)

end v1

end Compiler
