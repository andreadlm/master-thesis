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
                 | _      => τ -- TODO: error state
    | DEC x   => match (τ x).head? with
                 | some v => [x ↦ ((v - 1) :: (τ x).tail)] τ
                 | none   => τ
    | INC x   => match (τ x).head? with
                 | some v => [x ↦ ((v + 1) :: (τ x).tail)] τ
                 | none   => τ -- TODO: error state
    | SEQ P Q => (eval Q) (eval P τ)
    | FOR x P => match (τ x).head? with
                 | some v => match v with
                             | Int.ofNat   k => (fun τ' => eval P τ' )^[k] τ
                             | Int.negSucc k => (fun τ' => evalI P τ')^[k.succ] τ
                 | none   => τ -- TODO: error state

  def evalI (P : com) (τ : store) : store :=
    match P with
    | SKIP    => τ
    | CON x   => match τ x with
                 | 0 :: t => [x ↦ t] τ
                 | _      => τ -- TODO: error state
    | NOC x   => [x ↦ (0 :: (τ x))] τ
    | DEC x   =>  match (τ x).head? with
                 | some v => [x ↦ ((v + 1) :: (τ x).tail)] τ
                 | none   => τ -- TODO: error state
    | INC x   => match (τ x).head? with
                 | some v => [x ↦ ((v - 1) :: (τ x).tail)] τ
                 | none   => τ -- TODO: error state
    | SEQ P Q => (evalI Q) (evalI P τ)
    | FOR x P => match (τ x).head? with
                 | some v => match v with
                             | Int.ofNat   k => (fun τ' => evalI P τ')^[k] τ
                             | Int.negSucc k => (fun τ' => eval P τ' )^[k.succ] τ
                 | none   => τ -- TODO: error state
end

theorem inv_evalI (P : com) (τ : store) : eval (inv P) τ = evalI P τ := sorry

end SCORE
