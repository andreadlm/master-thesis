import MasterThesis.LOOP.Parser

open LOOP Com

def test_parser {α : Type} [BEq α] (name : String) (parser : Lean.Parsec α) (text : String) (expected : α) (error : Bool) : String :=
  let success_msg := s!"✔️ Test [{name}] passed"
  let failure_msg := s!"❌ Test [{name}] failed"

  match Lean.Parsec.run parser text with
  | .ok actual => if and (not error) (expected == actual) then success_msg
                  else failure_msg
  | .error _   => if error then success_msg
                  else failure_msg

def test1 : String :=
"x = 0;
x += 1;
y = x;
LOOP y DO
  x += 1
END"

def expected1 : LOOP.Com :=
  ZER "x";;
  INC "x";;
  ASN "y" "x";;
  LOOP "y" (
    INC "x"
  )

#eval test_parser "Basic program" parse test1 expected1 false

def test2 : String :=
"

x = 0;
y = 0;
x += 1;
LOOP x DO
  y = x
END

"

def expected2 : LOOP.Com :=
  ZER "x";;
  ZER "y";;
  INC "x";;
  LOOP "x" (
    ASN "y" "x"
  )

#eval test_parser "Newlines before and after" parse test2 expected2 false

def test3 : String :=
"
x = 0;
y = 0;
x += 1;
LOOP x DO
  y = 0;
  y += 1;
  y = x
END
"

def expected3 : LOOP.Com :=
  ZER "x";;
  ZER "y";;
  INC "x";;
  LOOP "x" (
    ZER "y";;
    INC "y";;
    ASN "y" "x"
  )

#eval test_parser "Multiple instructions in loop" parse test3 expected3 false

def test4 : String :=
"
x = 0;
y = 0;
x += 1;
LOOP x DO
  LOOP y DO
    x += 1
  END
END
"

def expected4 : LOOP.Com :=
  ZER "x";;
  ZER "y";;
  INC "x";;
  LOOP "x" (
    LOOP "y" (
      INC "x"
    )
  )

#eval test_parser "Nested loops" parse test4 expected4 false

def test5 : String :=
"
  x = 0;

    y = 0;

x += 1;

  LOOP x DO
      y = x
    END
"

def expected5 : LOOP.Com :=
  ZER "x";;
  ZER "y";;
  INC "x";;
  LOOP "x" (
    ASN "y" "x"
  )

#eval test_parser "Whitespaces around instructions" parse test5 expected5 false

def test6 : String :=
"x = 0; y = 0"

def expected6 : LOOP.Com :=
  ZER "x";;
  ZER "y"

#eval test_parser "Multiple instructions on same row" parse test6 expected6 false

def test7 : String :=
"LOOP x DO
  x = 0; y = 0
END; x += 1"

def expected7 : LOOP.Com :=
  LOOP "x" (
    ZER "x";;
    ZER "y"
  );;
  INC "x"

#eval test_parser "Multiple instructions on same row complex" parse test7 expected7 false
