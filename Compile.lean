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

def whitespace : Parsec Unit := do
  let _ ← many $ satisfy $ fun c => c == ' ' || c == '\t'

def lexeme {α : Type} (p : Parsec α) : Parsec α := do
  let x ← p
  whitespace
  return x

def newline : Parsec Unit := do
  skipChar '\n'
  let _ ← many $ satisfy $ fun c => c == '\n' || c == ' ' || c == '\t'

def program {α : Type} (p : Parsec α) : Parsec α := do
  let x ← p
  eof
  return x

mutual
  partial def pProgram : Parsec LOOP.Com :=
    program $ pCom

  partial def pCom : Parsec LOOP.Com :=
    attempt pSEQ  <|> pSingle

  partial def pSingle : Parsec LOOP.Com :=
    attempt pSKIP <|>
    attempt pZER  <|>
    attempt pASN  <|>
    attempt pINC  <|>
            pFOR

  partial def pSKIP : Parsec LOOP.Com := do
    lexeme $ skipString $ "SKIP"
    return LOOP.Com.SKIP

  partial def pZER : Parsec LOOP.Com := do
    let i ← lexeme $ var
    lexeme $ skipChar '='
    lexeme $ skipChar '0'
    return LOOP.Com.ZER i

  partial def pASN : Parsec LOOP.Com := do
    let i1 ← lexeme $ var
    lexeme $ skipChar '='
    let i2 ← lexeme $ var
    return LOOP.Com.ASN i1 i2

  partial def pINC : Parsec LOOP.Com := do
    let i ← lexeme $ var
    lexeme $ skipString "+="
    lexeme $ skipChar '1'
    return LOOP.Com.INC i

  partial def pSEQ : Parsec LOOP.Com := do
    let P ← pSingle
    newline
    let Q ← pCom
    return LOOP.Com.SEQ P Q

  partial def pFOR := do
    lexeme $ skipString "LOOP"
    let i ← lexeme $ var
    newline
    let body ← pCom
    newline
    lexeme $ skipString "END"
    return LOOP.Com.FOR i body
end

#eval Lean.Parsec.run pProgram "SKIP"
#eval Lean.Parsec.run pProgram "x = 0"
#eval Lean.Parsec.run pProgram "x = y"
#eval Lean.Parsec.run pProgram "x += 1"
#eval Lean.Parsec.run pProgram "LOOP x1 \n x += 1 \n END"
#eval Lean.Parsec.run pProgram "x2 += 1 \n x1 = x2"

def test : String :=
  "x1 = 0
   x2 = 0
   LOOP x1
     x2 += 1
     x1 = x2
     LOOP x2
       x3 = 0
       x3 += 1
       x1 = 0
     END
  END"

#eval Lean.Parsec.run pCom test
