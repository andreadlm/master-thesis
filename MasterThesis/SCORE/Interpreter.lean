import MasterThesis.SCORE.Language
import Mathlib.Logic.Function.Iterate

namespace SCORE

open SCORE Com

mutual
  def eval (P : Com) (s : State) : State :=
    match s with
    | none   => none
    | some σ =>
      match P with
      | SKIP    => s
      | CON x   => some ([x ↦ (0 :: (σ x))] σ)
      | NOC x   => match (σ x).head? with
                   | some 0 => some ([x ↦ (σ x).tail] σ)
                   | _      => none
      | DEC x   => match (σ x).head? with
                   | some v => some ([x ↦ ((v - 1) :: (σ x).tail)] σ)
                   | none   => none
      | INC x   => match (σ x).head? with
                   | some v => some ([x ↦ ((v + 1) :: (σ x).tail)] σ)
                   | none   => none
      | SEQ P Q => (eval Q) (eval P s)
      | FOR x P => match (σ x).head? with
                   | some v => match v with
                               | Int.ofNat   k => (fun t => eval  P t)^[k] s
                               | Int.negSucc k => (fun t => evalI P t)^[k.succ] s
                   | none   => none
  def evalI (P : Com) (s : State) : State :=
    match s with
    | none   => none
    | some σ =>
      match P with
      | SKIP    => s
      | CON x   => match (σ x).head? with
                   | some 0 => some ([x ↦ (σ x).tail] σ)
                   | _   => none
      | NOC x   => some ([x ↦ (0 :: (σ x))] σ)
      | DEC x   => match (σ x).head? with
                   | some v => some ([x ↦ ((v + 1) :: (σ x).tail)] σ)
                   | none   => none
      | INC x   => match (σ x).head? with
                   | some v => some ([x ↦ ((v - 1) :: (σ x).tail)] σ)
                   | none   => none
      | SEQ P Q => (evalI Q) (evalI P s)
      | FOR x P => match (σ x).head? with
                   | some v => match v with
                               | Int.ofNat   k => (fun t => evalI P t)^[k] s
                               | Int.negSucc k => (fun t => eval  P t)^[k.succ] s
                   | none   => none
end

end SCORE
