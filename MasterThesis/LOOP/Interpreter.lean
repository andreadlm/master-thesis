import Mathlib.Logic.Function.Iterate

import MasterThesis.LOOP.Language

namespace LOOP

open LOOP.Com

def eval (P : Com) (s : State) : State :=
  match s with
  | none   => none
  | some σ =>
    match P with
    | SKIP    => some σ
    | ZER x   => some ([x ↦ 0] σ)
    | ASN x y => some ([x ↦ (σ y)] σ)
    | INC x   => some ([x ↦ ((σ x) + 1)] σ)
    | SEQ P Q => (eval Q) (eval P σ)
    | FOR x P => (fun σ' => (eval P σ'))^[σ x] σ

end LOOP
