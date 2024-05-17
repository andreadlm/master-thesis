import MasterThesis.SCORE.Language
import MasterThesis.SCORE.Functions

namespace SCORE

open SCORE.com

mutual
  def eval (P : com) (s : store) : store :=
    match P with
    | SKIP    => s
    | CON x   => store.update x (0 :: (s x)) s
    | NOC x   => match s x with
                 | 0 :: t => store.update x t s
                 | _      => s -- CHECK: error?
    | DEC x   => store.update x (((s x).head! - 1) :: (s x).tail!) s
    | INC x   => store.update x (((s x).head! + 1) :: (s x).tail!) s
    | SEQ P Q => (eval Q) (eval P s)
    | FOR x P => match (s x).head! with
                 | Int.ofNat   v => Nat.iterate (fun s' => eval P s') v s
                 | Int.negSucc v => Nat.iterate (fun s' => evalI P s') (Nat.succ v) s

  def evalI (P : com) (s : store) : store :=
    match P with
    | SKIP    => s
    | CON x   => match s x with
                 | 0 :: t => store.update x t s
                 | _      => s -- CHECK: error?
    | NOC x   => store.update x (0 :: (s x)) s
    | DEC x   => store.update x (((s x).head! + 1) :: (s x).tail!) s
    | INC x   => store.update x (((s x).head! - 1) :: (s x).tail!) s
    | SEQ P Q => (evalI P) (evalI Q s)
    | FOR x P => match (s x).head! with
                 | Int.ofNat   v => Nat.iterate (fun s' => evalI P s') v s
                 | Int.negSucc v => Nat.iterate (fun s' => eval P s') (Nat.succ v) s
end

theorem inv_evalI (P : com) (s : store): eval (inv P) s = evalI P s := sorry

end SCORE
