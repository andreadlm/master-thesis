import Mathlib.Logic.Function.Iterate

import MasterThesis.Commons

namespace LOOP

def store : Type := ident → Nat

namespace store

def update (x : ident) (v : Nat) (s : store) : store :=
  fun (y : ident) => if x == y then v else (s y)

theorem update_same (s : store) (x y : ident) (v : Nat) : x == y → (store.update x v s) y = v := by
  intros
  unfold update
  apply if_pos
  assumption

theorem update_other (s : store) (x y : ident) (v : Nat) : ¬(x == y) → (store.update x v s) y = (s y) := by
  intros
  unfold update
  apply if_neg
  assumption

end store

inductive com : Type
| SKIP : com
| ZER : ident → com
| ASN : ident → ident → com
| INC : ident → com
| SEQ : com → com → com
| FOR : ident → com → com
deriving Repr

open com

infixl:80 ";;" => SEQ

end LOOP
