/- Ispirato a https://jakewheat.github.io/intro_to_parsing/ -/

import MasterThesis
import Lean.Data.Parsec

open Lean Parsec

def main (args : List String) : IO UInt32  :=
  match args with
  | [inputFile, outputFile] => do
    try
      let inputText ← IO.FS.readFile inputFile
      IO.FS.writeFile outputFile inputText
      return 0
    catch e : IO.Error => do
      IO.eprint s!"Error: {e}"
      return 1
  | _ => do
    IO.eprint s!"Error: expected two arguments, got {args.length}"
    return 1

def var : Parsec String := do
    let fc ← firstChar
    let rest ← many nonFirstChar
    return ⟨fc :: rest.toList⟩
  where
    firstChar := satisfy Char.isAlpha
    nonFirstChar := satisfy $ fun c => c.isAlpha || c.isDigit || c == '_'

#eval Lean.Parsec.run var "x"
#eval Lean.Parsec.run var "xyz"
#eval Lean.Parsec.run var "_x"
#eval Lean.Parsec.run var "1x"

-- TODO: controllare
def whitespace : Parsec Unit := do
  let _ ← many $ satisfy $ fun c => c == ' ' || c == '\t'

#eval Lean.Parsec.run whitespace ""
#eval Lean.Parsec.run whitespace " "
#eval Lean.Parsec.run whitespace "  "
#eval Lean.Parsec.run whitespace "\t"

def lexeme {α : Type} (p : Parsec α) : Parsec α := do
  let x ← p
  whitespace
  return x

def newline : Parsec Unit := lexeme $ do
  let _ ← many1 $ satisfy $ fun c => c == '\n'

def instruction {α : Type} (p : Parsec α) : Parsec α := do
  let x ← p
  newline
  return x

def pSKIP : Parsec LOOP.Com := instruction $ do
  lexeme $ skipString $ "SKIP"
  return LOOP.Com.SKIP

#eval Lean.Parsec.run pSKIP "SKIP \n"

def pZER : Parsec LOOP.Com := instruction $ do
  let i ← lexeme $ var
  lexeme $ skipChar '='
  lexeme $ skipChar '0'
  return LOOP.Com.ZER i

#eval Lean.Parsec.run pZER "x1 = 0 \n"

def pASN : Parsec LOOP.Com := instruction $ do
  let i1 ← lexeme $ var
  lexeme $ skipChar '='
  let i2 ← lexeme $ var
  return LOOP.Com.ASN i1 i2

#eval Lean.Parsec.run pASN "x1 = x2 \n"

def pINC : Parsec LOOP.Com := instruction $ do
  let i ← lexeme $ var
  lexeme $ skipChar '='
  lexeme $ skipString i
  lexeme $ skipChar '+'
  lexeme $ skipChar '1'
  return LOOP.Com.INC i

#eval Lean.Parsec.run pINC "x1 = x1 + 1 \n"

def pSingle : Parsec LOOP.Com :=
  attempt pSKIP <|>
  attempt pZER  <|>
  attempt pASN  <|>
  attempt pINC

#eval Lean.Parsec.run pSingle "SKIP \n"
#eval Lean.Parsec.run pSingle "x1 = 0 \n"
#eval Lean.Parsec.run pSingle "x1 = x2 \n"
#eval Lean.Parsec.run pSingle "x1 = x1 + 1 \n"

def pFOR : Parsec LOOP.Com := instruction $ do
  lexeme $ skipString "LOOP"
  let i ← lexeme $ var
  newline
  let body ← pSingle
  lexeme $ skipString "END"
  return LOOP.Com.FOR i body

#eval Lean.Parsec.run pFOR "LOOP x \n x = 0 \n END \n"
