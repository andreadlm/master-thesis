/-
"A LEAN-certified reversibilization of Meyer-Ritchie LOOP language".
Master thesis in computer science, University of Turin.
Authors: Andrea Delmastro
-/
import MasterThesis.Commons

/-!
# SCORE language

This file defines SCORE, a simple reversible programming language.

## Implementation notes

## References

-/

namespace SCORE

def Store : Type := Ident → List Int

namespace Store

def emp : Store := fun _ => []

def update (x : Ident) (l : List Int) (σ : Store) : Store :=
  fun (y : Ident) => if x = y then l else (σ y)

notation:65 "[" x:65 " ↦ " l:65 "]"      => update x l emp
notation:65 "[" x:65 " ↦ " l:65 "]" s:65 => update x l s

end Store

abbrev State := Option Store

namespace State

notation "⊥" => (none : State)

end State

inductive Com : Type
| SKIP : Com
| CON  : Ident → Com
| NOC  : Ident → Com
| DEC  : Ident → Com
| INC  : Ident → Com
| SEQ  : Com → Com → Com
| FOR  : Ident → Com → Com
deriving BEq

open Com

infixr:80 ";;" => SEQ

def comToString (indLv : Nat) (P : Com) : String :=
  let rec ind (indLv : Nat) : String :=
    match indLv with
    | .zero   => ""
    | .succ m => "  " ++ ind m
  match P with
  | SKIP    => s!"{ind indLv}SKIP"
  | CON x   => s!"{ind indLv}CON {x}"
  | NOC x   => s!"{ind indLv}NOC {x}"
  | DEC x   => s!"{ind indLv}DEC {x}"
  | INC x   => s!"{ind indLv}INC {x}"
  | SEQ P Q => s!"{comToString indLv P}\n{comToString indLv Q}"
  | FOR x P => s!"{ind indLv}FOR {x}\n{comToString (indLv + 1) P}"

instance : ToString Com where
  toString := comToString 0

#eval (SEQ (FOR "x" (SEQ (SEQ (CON "x") (FOR "x" (SEQ (CON "x") (NOC "y")))) (INC "x"))) (DEC "x"))

def inv (P : Com) : Com :=
  match P with
  | SKIP    => SKIP
  | CON x   => NOC x
  | NOC x   => CON x
  | DEC x   => INC x
  | INC x   => DEC x
  | SEQ P Q => SEQ (inv Q) (inv P)
  | FOR x Q => FOR x (inv Q)

postfix:max "⁻¹" => inv

end SCORE
