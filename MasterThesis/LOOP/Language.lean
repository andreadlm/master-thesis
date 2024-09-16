/-
"A LEAN-certified reversibilization of Meyer-Ritchie LOOP language".
Master thesis in computer science, University of Turin.
Author: Andrea Delmastro
-/
import Mathlib.Logic.Function.Iterate
import MasterThesis.Commons

/-!
# LOOP language

This file defines LOOP, a simple imperative nonreversible programming language that precisely
captures all the primitive recursive functions.

## Notations
* `[x ↦ v]` stands for `update emp x v` where `emp` is the empty state (_set the value of`x` to `v`in `emp`_)
* `σ[x ↦ v]` stands for `update σ x v` (_set the value of `x` to `v` in `σ`_)


## Implementation notes

A LOOP `State` is defined as an `Option Store` to provide a uniform structure for both LOOP and
SCORE states, simplifying the management of the notion of equivalence. The term `none` can be
interpreted as the failure state, even though this is not defined in the language specifications,
nor is meaningful.

## References

See [MeyerRitchie:Loop] for the original account on LOOP language.
-/

namespace LOOP

/-- A `Store` provides an abstract representation of memory in the form of a total function from
`Ident` to `Nat`. -/
def Store : Type := Ident → Nat

namespace Store

/-- An empty `Store` maps every identifier to zero. -/
def emp : Store := fun _ => 0

/-- Updates a `Store` by mapping the register identified by `x` to a new value `v`. -/
def update (σ : Store) (x : Ident) (v : Nat) : Store :=
  fun (y : Ident) => if x = y then v else (σ y)

notation:65 "[" x:65 " ↦ " v:65 "]"      => update emp x v
notation:65 σ:65 "[" x:65 " ↦ " v:65 "]" => update σ x v

end Store

/-- A `State` can be a `Store` or a failure. -/
abbrev State := Option Store

namespace State

notation "⊥" => (none : State)

end State

/-- A LOOP program is a sequence of commands chosen from skip, clearing a register, incrementing a
register, copying one register to another, composing two commands, and iterating over a finite
number of steps. -/
inductive Com : Type
| SKIP : Com
| ZER  : Ident → Com
| ASN  : Ident → Ident → Com
| INC  : Ident → Com
| SEQ  : Com → Com → Com
| LOOP : Ident → Com → Com
deriving BEq

namespace Com

infixr:80 ";;" => SEQ

/-- Computes the string representation of a LOOP command. -/
def comToString (indLv : Nat) (P : Com) : String :=
  let rec ind (indLv : Nat) : String :=
    match indLv with
    | .zero   => ""
    | .succ m => "  " ++ ind m
  match P with
  | SKIP     => s!"{ind indLv}SKIP"
  | ZER x    => s!"{ind indLv}{x} = 0"
  | ASN x y  => s!"{ind indLv}{x} = {y}"
  | INC x    => s!"{ind indLv}{x} += 1"
  | SEQ P Q  => s!"{comToString indLv P}\n{comToString indLv Q}"
  | LOOP x P => s!"{ind indLv}LOOP {x} DO\n{comToString (indLv + 1) P}\n{ind indLv}END"

instance : ToString Com where
  toString := comToString 0

end Com

/-- Interpreter for LOOP. The interpreter takes as input a `Com` and an evaluation `State` and
outputs the resulting `State` obtained by applying the command to the initial state. -/
def eval (P : Com) (s : State) : State :=
  match s with
  | ⊥      => ⊥
  | some σ =>
    match P with
    | .SKIP     => σ
    | .ZER x    => σ[x ↦ 0]
    | .ASN x y  => σ[x ↦ (σ y)]
    | .INC x    => σ[x ↦ ((σ x) + 1)]
    | .SEQ P Q  => (eval Q) (eval P σ)
    | .LOOP x P => (fun σ' => (eval P σ'))^[σ x] σ

end LOOP
