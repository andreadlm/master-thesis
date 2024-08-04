import MasterThesis.Commons

namespace LOOP

def Store : Type := Ident → Nat

namespace Store

def emp : Store := fun _ => 0

def update (x : Ident) (v : Nat) (s : Store) : Store :=
  fun (y : Ident) => if x = y then v else (s y)

notation:100 "[" x:100 " ↦ " v:100 "]" s:100 => update x v s -- Migliorare?
notation:100 "[" x:100 " ↦ " v:100 "]"       => [x ↦ v] emp -- Migliorare?

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
  let rec ind (indLv : Nat) : String :=
    match indLv with
    | .zero   => ""
    | .succ m => "  " ++ ind m
  match P with
  | SKIP    => s!"{ind indLv}SKIP"
  | ZER x   => s!"{ind indLv}{x} = 0"
  | ASN x y => s!"{ind indLv}{x} = {y}"
  | INC x   => s!"{ind indLv}{x} += 1"
  | SEQ P Q => s!"{comToString indLv P}\n{comToString indLv Q}"
  | FOR x P => s!"{ind indLv}LOOP {x}\n{comToString (indLv + 1) P}\n{ind indLv}END"

instance : ToString Com where
  toString := comToString 0

#eval (SEQ (FOR "x" (SEQ (SEQ (ZER "x") (FOR "x" (SEQ (ASN "x" "y") (INC "y")))) (INC "x"))) (ZER "x"))

end LOOP
