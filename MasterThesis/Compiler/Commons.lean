import MasterThesis.LOOP.Language
import MasterThesis.SCORE.Language

def eq_states (s : LOOP.State) (t : SCORE.State) : Prop :=
  match s, t with
  | some σ, some τ => ∀ (x : Ident), some ↑(σ x) = (τ x).head?
  | _     , _      => False

infix:50 "=ₛ" => eq_states
