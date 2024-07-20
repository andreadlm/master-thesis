import MasterThesis.LOOP.Functions
import MasterThesis.SCORE.Compiler_v1

open SCORE

def store0 : Store := ["x" ↦ [0]] ["y" ↦ [3]] ["z" ↦ [0]]

def storePred : Store := (eval (L2S LOOP.func.pred) store0)
#eval  storePred "x"
def storePredᵢ : Store := (evalI (L2S LOOP.func.pred) storePred)
#eval storePredᵢ "y"
