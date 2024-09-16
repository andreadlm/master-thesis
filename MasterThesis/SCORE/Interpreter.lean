import MasterThesis.SCORE.Language
import Mathlib.Logic.Function.Iterate

namespace SCORE

open SCORE Com

mutual
  def eval (P : Com) (s : State) : State :=
    match s with
    | ⊥      => ⊥
    | some σ =>
      match P with
      | SKIP    => s
      | CON x   => σ[x ↦ (0 :: (σ x))]
      | NOC x   => match (σ x).head? with
                   | some 0 => σ[x ↦ (σ x).tail]
                   | _      => ⊥
      | DEC x   => match (σ x).head? with
                   | some v => σ[x ↦ ((v - 1) :: (σ x).tail)]
                   | none   => ⊥
      | INC x   => match (σ x).head? with
                   | some v => σ[x ↦ ((v + 1) :: (σ x).tail)]
                   | none   => ⊥
      | SEQ P Q => (eval Q) (eval P s)
      | FOR x P => match (σ x).head? with
                   | some v => match v with
                               | Int.ofNat   k => (fun t => eval  P t)^[k] s
                               | Int.negSucc k => (fun t => evalI P t)^[k.succ] s
                   | none   => ⊥
  def evalI (P : Com) (s : State) : State :=
    match s with
    | ⊥      => ⊥
    | some σ =>
      match P with
      | SKIP    => s
      | CON x   => match (σ x).head? with
                   | some 0 => σ[x ↦ (σ x).tail]
                   | _   => ⊥
      | NOC x   => σ [x ↦ (0 :: (σ x))]
      | DEC x   => match (σ x).head? with
                   | some v => σ[x ↦ ((v + 1) :: (σ x).tail)]
                   | none   => ⊥
      | INC x   => match (σ x).head? with
                   | some v => σ[x ↦ ((v - 1) :: (σ x).tail)]
                   | none   => ⊥
      | SEQ P Q => (evalI Q) (evalI P s)
      | FOR x P => match (σ x).head? with
                   | some v => match v with
                               | Int.ofNat   k => (fun t => evalI P t)^[k] s
                               | Int.negSucc k => (fun t => eval  P t)^[k.succ] s
                   | none   => ⊥
end

end SCORE
