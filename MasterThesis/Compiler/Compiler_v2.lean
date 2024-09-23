/-
"A Lean-certified reversibilization of Meyer-Ritchie LOOP language".
Master thesis in computer science, University of Turin.
Authors: Andrea Delmastro
-/
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

lemma eq_states_idents_subs {s : LOOP.State} {t : SCORE.State} {a b : Finset Ident} : s ∼[a ∪ b] t → s ∼[a] t := by sorry

end Compiler
