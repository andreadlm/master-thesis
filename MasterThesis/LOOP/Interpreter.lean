import MasterThesis.LOOP.Language

namespace LOOP

open LOOP.com

def eval (P : com) (s : store) : store :=
  match P with
  | SKIP    => s
  | ZER x   => store.update x 0 s
  | ASN x y => store.update x (s y) s
  | INC x   => store.update x ((s x) + 1) s
  | SEQ P Q => (eval Q) (eval P s)
  | FOR x P => Nat.iterate (fun s' => (eval P s')) (s x) s

end LOOP
