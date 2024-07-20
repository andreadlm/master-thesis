import MasterThesis.LOOP.Language

namespace LOOP

open LOOP.Com

def eval (P : Com) (σ : Store) : Store :=
  match P with
  | SKIP    => σ
  | ZER x   => Store.update x 0 σ
  | ASN x y => Store.update x (σ y) σ
  | INC x   => Store.update x ((σ x) + 1) σ
  | SEQ P Q => (eval Q) (eval P σ)
  | FOR x P => (fun σ' => (eval P σ'))^[σ x] σ

end LOOP
