import Mathlib.Tactic.Basic
import Mathlib.Logic.Basic
import MasterThesis.LOOP.Language

open LOOP Store

@[simp]
lemma update_same {s : Store} {x y : Ident} {v : Nat} : x = y → (update x v s) y = v := by
  intros
  unfold update
  apply if_pos
  assumption

@[simp]
lemma update_other {s : Store} {x y : Ident} {v : Nat} : x ≠ y → (update x v s) y = (s y) := by
  intros
  unfold update
  apply if_neg
  assumption

@[simp]
lemma update_no_update {s : Store} {x : Ident} : (update x (s x) s) = s := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => rw[update_same ‹x = y›, ‹x = y›]
  | inr /- x ≠ y -/ => rw[update_other ‹x ≠ y›]
