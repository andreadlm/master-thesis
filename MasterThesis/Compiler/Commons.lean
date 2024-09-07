import Mathlib.Data.Finset.Basic
import MasterThesis.LOOP.Language
import MasterThesis.SCORE.Language

def eq_states (s : LOOP.State) (t : SCORE.State) : Prop :=
  match s, t with
  | some σ, some τ => ∀ (x : Ident), some ↑(σ x) = (τ x).head?
  | _     , _      => False

infix:50 "=ₛ" => eq_states

def eq_states_idents (s : LOOP.State) (t : SCORE.State) (ids : Finset Ident) : Prop :=
  match s, t with
  | some σ, some τ => ∀ (x : Ident), x ∈ ids → some ↑(σ x) = (τ x).head?
  | _     , _      => False

notation:50 s:50 "=[" P:50 "]ₛ" t:50 => eq_states_idents s t P

namespace SCORE.Com

def ids (P : SCORE.Com) : Finset Ident :=
  match P with
  | SKIP    => {}
  | CON x   => {x}
  | NOC x   => {x}
  | DEC x   => {x}
  | INC x   => {x}
  | SEQ P Q => ids P ∪ ids Q
  | FOR x P => {x} ∪ ids P

end SCORE.Com

namespace LOOP.Com

def ids (P : LOOP.Com) : Finset Ident :=
  match P with
  | SKIP     => {}
  | ZER x    => {x}
  | ASN x y  => {x, y}
  | INC x    => {x}
  | SEQ P Q  => ids P ∪ ids Q
  | LOOP x P => {x} ∪ ids P

end LOOP.Com
