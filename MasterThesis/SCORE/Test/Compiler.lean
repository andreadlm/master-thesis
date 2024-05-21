import MasterThesis.LOOP.Functions
import MasterThesis.SCORE.Compiler

open SCORE

def store0 : store := ["x" ↦ [0]] ["y" ↦ [3]] ["z" ↦ [0]]

def storePred : store := (eval (L2S LOOP.func.pred) store0)
#eval  storePred "x"
def storePredᵢ : store := (evalI (L2S LOOP.func.pred) storePred)
#eval storePredᵢ "y"
