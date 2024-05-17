import MasterThesis.LOOP.Functions
import MasterThesis.SCORE.Compiler

open SCORE

def store0 : SCORE.store := ["x" ↦ [0]] ["y" ↦ [3]] ["z" ↦ [0]]

#eval (eval (LOOP2SCORE LOOP.func.pred) store0) "x"
