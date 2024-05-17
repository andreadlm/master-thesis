import Mathlib.Logic.Function.Iterate

import MasterThesis.Commons

namespace SCORE

def store : Type := ident → List Int

namespace store

def emp : store := fun _ => []

def update (x : ident) (l : List Int) (s : store) : store :=
  fun (y : ident) => if x == y then l else (s y)

notation "[" x " ↦ " l "]" s => update x l s -- Migliorare?
notation "[" x " ↦ " l "]"   => [x ↦ l] emp -- Migliorare?

#eval (["z" ↦ [3]] ["y" ↦ [2]] ["x" ↦ [1]]) "x"

theorem update_same (s : store) (x y : ident) (l : List Int) : x == y → (store.update x l s) y = l := by
  intros
  unfold update
  apply if_pos
  assumption

theorem update_other (s : store) (x y : ident) (l : List Int) : ¬(x == y) → (store.update x l s) y = s y := by
  intros
  unfold update
  apply if_neg
  assumption

end store

inductive com : Type
| SKIP : com
| CON  : ident → com
| NOC  : ident → com
| DEC  : ident → com
| INC  : ident → com
| SEQ  : com → com → com
| FOR  : ident → com → com
deriving Repr

open com

infixl:80 ";;" => SEQ

def inv (P : com) : com :=
  match P with
  | SKIP    => SKIP
  | CON x   => NOC x
  | NOC x   => CON x
  | DEC x   => INC x
  | INC x   => DEC x
  | SEQ Q R => SEQ (inv R) (inv Q)
  | FOR x Q => FOR x (inv Q)

theorem inv_inv (P : com) : (inv (inv P)) = P := by
  induction  P
  case SKIP        => simp[inv]
  case CON         => simp[inv]
  case NOC         => simp[inv]
  case DEC         => simp[inv]
  case INC         => simp[inv]
  case SEQ ih₁ ih₂ => simp[inv, ih₁, ih₂]
  case FOR ih      => simp[inv, ih]

end SCORE
