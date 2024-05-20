import MasterThesis.SCORE.Language
import MasterThesis.SCORE.Functions

namespace SCORE

open SCORE.com

mutual
  def eval (P : com) (σ : store) : store :=
    match P with
    | SKIP    => σ
    | CON x   => [x ↦ (0 :: (σ x))] σ
    | NOC x   => match σ x with
                 | 0 :: t => [x ↦ t] σ
                 | _      => σ -- CHECK: error?
    | DEC x   => [x ↦ (((σ x).head! - 1) :: (σ x).tail!)] σ
    | INC x   => [x ↦ (((σ x).head! + 1) :: (σ x).tail!)] σ
    | SEQ P Q => (eval Q) (eval P σ)
    | FOR x P => match (σ x).head! with
                 | Int.ofNat   v => (fun τ  => eval P τ)^[v] σ
                 | Int.negSucc v => (fun τ => evalI P τ)^[v.succ] σ

  def evalI (P : com) (σ : store) : store :=
    match P with
    | SKIP    => σ
    | CON x   => match σ x with
                 | 0 :: t => [x ↦ t] σ
                 | _      => σ -- CHECK: error?
    | NOC x   => [x ↦ (0 :: (σ x))] σ
    | DEC x   => [x ↦ (((σ x).head! + 1) :: (σ x).tail!)] σ
    | INC x   => [x ↦ (((σ x).head! - 1) :: (σ x).tail!)] σ
    | SEQ P Q => (evalI P) (evalI Q σ)
    | FOR x P => match (σ x).head! with
                 | Int.ofNat   v => (fun τ => evalI P τ)^[v] σ
                 | Int.negSucc v => (fun τ => eval P τ)^[v.succ] σ
end

theorem inv_evalI (P : com) (σ : store) : eval (inv P) σ = evalI P σ := sorry

end SCORE
