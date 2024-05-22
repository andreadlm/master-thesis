import MasterThesis.SCORE.Language
import MasterThesis.SCORE.Functions

namespace SCORE

open SCORE.com

mutual
  def eval (P : com) (τ : store) : store :=
    match P with
    | SKIP    => τ
    | CON x   => [x ↦ (0 :: (τ x))] τ
    | NOC x   => match τ x with
                 | 0 :: t => [x ↦ t] τ
                 | _      => τ -- CHECK: error?
    | DEC x   => [x ↦ (((τ x).head! - 1) :: (τ x).tail!)] τ
    | INC x   => [x ↦ (((τ x).head! + 1) :: (τ x).tail!)] τ
    | SEQ P Q => (eval Q) (eval P τ)
    | FOR x P => match (τ x).head! with
                 | Int.ofNat   v => (fun τ'  => eval P τ')^[v] τ
                 | Int.negSucc v => (fun τ' => evalI P τ')^[v.succ] τ

  def evalI (P : com) (τ : store) : store :=
    match P with
    | SKIP    => τ
    | CON x   => match τ x with
                 | 0 :: t => [x ↦ t] τ
                 | _      => τ -- CHECK: error?
    | NOC x   => [x ↦ (0 :: (τ x))] τ
    | DEC x   => [x ↦ (((τ x).head! + 1) :: (τ x).tail!)] τ
    | INC x   => [x ↦ (((τ x).head! - 1) :: (τ x).tail!)] τ
    | SEQ P Q => (evalI Q) (evalI P τ)
    | FOR x P => match (τ x).head! with
                 | Int.ofNat   v => (fun τ' => evalI P τ')^[v] τ
                 | Int.negSucc v => (fun τ' => eval P τ')^[v.succ] τ
end

theorem inv_evalI (P : com) (τ : store) : eval (inv P) τ = evalI P τ := sorry

end SCORE
