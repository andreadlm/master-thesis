import MasterThesis.LOOP.Language

namespace LOOP

open LOOP.com

def eval (P : com) (σ : store) : store :=
  match P with
  | SKIP    => σ
  | ZER x   => store.update x 0 σ
  | ASN x y => store.update x (σ y) σ
  | INC x   => store.update x ((σ x) + 1) σ
  | SEQ P Q => (eval Q) (eval P σ)
  | FOR x P => (fun σ' => (eval P σ'))^[σ x] σ

end LOOP
