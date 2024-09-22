import Mathlib.Tactic.Basic
import MasterThesis.LOOP.Language
import MasterThesis.SCORE.Language
import MasterThesis.Compiler.Commons

lemma eq_states_idents_subs {s : LOOP.State} {t : SCORE.State} {a b : Finset Ident} : s =[a ∪ b]ₛ t → s =[a]ₛ t := by sorry
