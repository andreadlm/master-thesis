import Mathlib.Logic.Function.Iterate

import MasterThesis.SCORE.Language
import MasterThesis.SCORE.Functions

namespace SCORE

open SCORE.com SCORE.store SCORE.state

mutual
  def eval (P : com) (s : state) : state :=
    match s with
    | fail       => fail
    | prog σ =>
      match P with
      | SKIP    => s
      | CON x   => prog ([x ↦ (0 :: (σ x))] σ)
      | NOC x   => match (σ x).head? with
                   | some 0 => prog ([x ↦ (σ x).tail] σ)
                   | _      => fail
      | DEC x   => match (σ x).head? with
                   | some v => prog ([x ↦ ((v - 1) :: (σ x).tail)] σ)
                   | none   => fail
      | INC x   => match (σ x).head? with
                   | some v => prog ([x ↦ ((v + 1) :: (σ x).tail)] σ)
                   | none   => fail
      | SEQ P Q => (eval Q) (eval P s)
      | FOR x P => match (σ x).head? with
                   | some v => match v with
                               | Int.ofNat   k => (fun τ => eval  P τ)^[k] s
                               | Int.negSucc k => (fun τ => evalI P τ)^[k.succ] s
                   | none   => fail
  def evalI (P : com) (s : state) : state :=
    match s with
    | fail       => fail
    | prog σ =>
      match P with
      | SKIP    => s
      | CON x   => match (σ x).head? with
                   | some 0 => prog ([x ↦ (σ x).tail] σ)
                   | _   => fail
      | NOC x   => prog ([x ↦ (0 :: (σ x))] σ)
      | DEC x   => match (σ x).head? with
                   | some v => prog ([x ↦ ((v + 1) :: (σ x).tail)] σ)
                   | none   => fail
      | INC x   => match (σ x).head? with
                   | some v => prog ([x ↦ ((v - 1) :: (σ x).tail)] σ)
                   | none   => fail
      | SEQ P Q => (evalI Q) (evalI P s)
      | FOR x P => match (σ x).head? with
                   | some v => match v with
                               | Int.ofNat   k => (fun τ => evalI P τ)^[k] s
                               | Int.negSucc k => (fun τ => eval  P τ)^[k.succ] s
                   | none   => fail
end

end SCORE
