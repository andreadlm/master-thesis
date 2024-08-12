import Mathlib.Data.Finset.Basic
import MasterThesis.LOOP.Language
import MasterThesis.SCORE.Language

def eq_states (s : LOOP.State) (t : SCORE.State) : Prop :=
  match s, t with
  | some σ, some τ => ∀ (x : Ident), some ↑(σ x) = (τ x).head?
  | _     , _      => False

infix:50 "=ₛ" => eq_states

class PLang (α : Type) where
  idents : α → Finset Ident

def eq_states_idents {α : Type} [PLang α] (s : LOOP.State) (t : SCORE.State) (P : α) : Prop :=
  match s, t with
  | some σ, some τ => ∀ (x : Ident), x ∈ (PLang.idents P) → some ↑(σ x) = (τ x).head?
  | _     , _      => False

notation:50 s:50 "=[" P:50 "]ₛ" t:50 => eq_states_idents s t P

def SCOREcomIdents (P : SCORE.Com) : Finset Ident :=
  match P with
  | SCORE.Com.SKIP    => {}
  | SCORE.Com.CON x   => {x}
  | SCORE.Com.NOC x   => {x}
  | SCORE.Com.DEC x   => {x}
  | SCORE.Com.INC x   => {x}
  | SCORE.Com.SEQ P Q => SCOREcomIdents P ∪ SCOREcomIdents Q
  | SCORE.Com.FOR x P => {x} ∪ SCOREcomIdents P

instance : PLang SCORE.Com where
  idents := SCOREcomIdents

def LOOPcomIdents (P : LOOP.Com) : Finset Ident :=
  match P with
  | LOOP.Com.SKIP    => {}
  | LOOP.Com.ZER x   => {x}
  | LOOP.Com.ASN x y => {x, y}
  | LOOP.Com.INC x   => {x}
  | LOOP.Com.SEQ P Q => LOOPcomIdents P ∪ LOOPcomIdents Q
  | LOOP.Com.FOR x P => {x} ∪ LOOPcomIdents P

instance : PLang LOOP.Com where
  idents := LOOPcomIdents
