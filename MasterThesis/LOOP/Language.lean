import Mathlib.Logic.Function.Iterate

import MasterThesis.Commons

namespace LOOP

def Store : Type := Ident → Nat

namespace Store

def emp : Store := fun _ => 0

def update (x : Ident) (v : Nat) (s : Store) : Store :=
  fun (y : Ident) => if x = y then v else (s y)

notation:100 "[" x:100 " ↦ " v:100 "]" s:100 => update x v s -- Migliorare?
notation:100 "[" x:100 " ↦ " v:100 "]"       => [x ↦ v] emp -- Migliorare?

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

lemma update_no_update {s : Store} {x : Ident} : (update x (s x) s) = s := by
  funext y
  cases eq_or_ne x y with
  | inl /- x = y -/ => rw[update_same ‹x = y›, ‹x = y›]
  | inr /- x ≠ y -/ => rw[update_other ‹x ≠ y›]

end Store

inductive Com : Type
| SKIP : Com
| ZER : Ident → Com
| ASN : Ident → Ident → Com
| INC : Ident → Com
| SEQ : Com → Com → Com
| FOR : Ident → Com → Com

open Com

infixl:80 ";;" => SEQ

def comToString (indLv : Nat) (P : Com) : String :=
  let ind : String := (String.append "  ")^[indLv] ""
  match P with
  | SKIP    => s!"{ind}SKIP"
  | ZER x   => s!"{ind}{x} = 0"
  | ASN x y => s!"{ind}{x} = {y}"
  | INC x   => s!"{ind}{x} += 1"
  | SEQ P Q => s!"{comToString indLv P}\n{comToString indLv Q}"
  | FOR x P => s!"{ind}LOOP {x}\n{comToString (indLv + 1) P}\n{ind}END"

instance : ToString Com where
  toString := comToString 0

#eval (SEQ (FOR "x" (SEQ (SEQ (ZER "x") (FOR "x" (SEQ (ASN "x" "y") (INC "y")))) (INC "x"))) (ZER "x"))

end LOOP
