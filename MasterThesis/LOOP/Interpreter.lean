import Mathlib.Logic.Function.Iterate

import MasterThesis.LOOP.Language

namespace LOOP

open LOOP.Com

def eval (P : Com) (s : State) : State :=
  match s with
  | none   => none
  | some σ =>
    match P with
    | SKIP     => some σ
    | ZER x    => some (σ[x ↦ 0])
    | ASN x y  => some (σ[x ↦ (σ y)])
    | INC x    => some (σ[x ↦ ((σ x) + 1)])
    | SEQ P Q  => (eval Q) (eval P σ)
    | LOOP x P => (fun σ' => (eval P σ'))^[σ x] σ

end LOOP
