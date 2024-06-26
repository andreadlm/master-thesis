import Mathlib.Logic.Function.Iterate

import MasterThesis.Commons

namespace SCORE

def store : Type := ident → List Int

namespace store

def emp : store := fun _ => []

def update (x : ident) (l : List Int) (s : store) : store :=
  fun (y : ident) => if x = y then l else (s y)

notation:100 "[" x:100 " ↦ " l:100 "]" s:100 => update x l s -- Migliorare?
notation:100 "[" x:100 " ↦ " l:100 "]"       => [x ↦ l] emp -- Migliorare?

#eval (["z" ↦ [3]] ["y" ↦ [2]] ["x" ↦ [1]]) "x"

@[simp]
lemma update_same {s : store} {x y : ident} {l : List Int} : x = y → (store.update x l s) y = l := by
  intros; simp only [if_pos ‹x = y›, update]

@[simp]
lemma update_other {s : store} {x y : ident} {l : List Int} : x ≠ y → (store.update x l s) y = s y := by
  intros; simp only [if_neg ‹x ≠ y›, update]

lemma update_shrink {s : store} {x : ident} {l₁ l₂ : List Int} : (store.update x l₂ (store.update x l₁ s)) = store.update x l₂ s := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => simp only [update_same ‹x = y›]
  | inr /- x ≠ y -/ => simp only [update_other ‹x ≠ y›]

lemma update_unchanged {s : store} {x : ident} : s = store.update x (s x) s := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => rewrite [‹x = y›]; simp only [update_same]
  | inr /- x ≠ y -/ => simp only [update_other ‹x ≠ y›]

lemma update_unchanged_cons {s : store} {x : ident} {v : Int} : (s x).head? = some v → s = store.update x (v :: (s x).tail) s := by
  intro
  have : (v :: (s x).tail) = (s x) := by
    sorry
  simp only [‹(v :: (s x).tail) = (s x)›]
  apply update_unchanged

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
