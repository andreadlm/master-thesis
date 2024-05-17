import MasterThesis.LOOP.Interpreter
import MasterThesis.LOOP.Functions

open LOOP LOOP.func

def store0 : store := ["x" ↦ 2] ["y" ↦ 3] ["z" ↦ 0]
def store1 : store := ["x" ↦ 0] ["y" ↦ 2] ["z" ↦ 0]

#eval (eval sum store0) "z"

#eval (eval pred store1) "x"
