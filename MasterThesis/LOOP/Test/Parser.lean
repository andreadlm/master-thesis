import MasterThesis.LOOP.Parser

open LOOP Com

def test {α : Type} [BEq α] (name : String) (expected : α) (actual : α) : String :=
  if expected == actual then s!"✔️ Test {name} passed"
  else s!"❌ Test [{name}] failed"

def test_parser {α : Type} [BEq α] (name : String) (parser : Lean.Parsec α) (text : String) (expected : α) : String :=
  match Lean.Parsec.run parser text with
  | .ok actual => test name expected actual
  | .error e   => s!"❌ Test [{name}] failed : {e}"

def test1 : String :=
"x = 0
x += 1
y = x
LOOP y
  x += 1
END"

def expected1 : LOOP.Com :=
  ZER "x" ;;
  INC "x" ;;
  ASN "y" "x" ;;
  FOR "y" (
    INC "x"
  )

#eval test_parser "test 1" parse test1 expected1
