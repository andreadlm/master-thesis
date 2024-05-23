import Mathlib.Logic.Function.Iterate

import MasterThesis.Commons

namespace LOOP

def store : Type := ident → Nat

namespace store

def emp : store := fun _ => 0

def update (x : ident) (v : Nat) (s : store) : store :=
  fun (y : ident) => if x = y then v else (s y)

notation:100 "[" x:100 " ↦ " v:100 "]" s:100 => update x v s -- Migliorare?
notation:100 "[" x:100 " ↦ " v:100 "]"       => [x ↦ v] emp -- Migliorare?

@[simp]
lemma update_same {s : store} {x y : ident} {v : Nat} : x = y → (store.update x v s) y = v := by
  intros
  unfold update
  apply if_pos
  assumption

@[simp]
lemma update_other {s : store} {x y : ident} {v : Nat} : x ≠ y → (store.update x v s) y = (s y) := by
  intros
  unfold update
  apply if_neg
  assumption

lemma update_no_update {s : store} {x : ident} : (update x (s x) s) = s := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => rw[update_same ‹x = y›, ‹x = y›]
  | inr /- x ≠ y -/ => rw[update_other ‹x ≠ y›]

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
