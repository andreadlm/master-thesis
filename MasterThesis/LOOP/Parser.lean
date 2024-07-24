/- References
  * https://jakewheat.github.io/intro_to_parsing/
  * https://wiki.haskell.org/Parsing_a_simple_imperative_language
  * https://leanprover-community.github.io/mathlib4_docs/Lean/Data/Json/Parser.html
-/

import Lean.Data.Parsec

import MasterThesis.LOOP.Language

open Lean Parsec
open LOOP Com

def var : Parsec String := do
    let fc ← firstChar
    let rest ← many nonFirstChar
    return ⟨fc :: rest.toList⟩
  where
    firstChar := satisfy Char.isAlpha
    nonFirstChar := satisfy <| fun c => c.isAlpha || c.isDigit || c == '_'

def whitespace : Parsec Unit := do
  let _ ← many <| satisfy fun c => c == ' ' || c == '\t'

def lexeme {α : Type} (p : Parsec α) : Parsec α := do
  let x ← p
  whitespace
  return x

def newline : Parsec Unit := do
  skipChar '\n'
  ws

mutual
  partial def parse : Parsec Com := do
    ws
    let prog ← pCom
    ws
    eof
    return prog

  partial def pCom : Parsec Com :=
    attempt pSEQ  <|> pSingle

  partial def pSingle : Parsec Com :=
    attempt pSKIP <|>
    attempt pZER  <|>
    attempt pASN  <|>
    attempt pINC  <|>
            pFOR

  partial def pSKIP : Parsec Com := do
    lexeme <| skipString "SKIP"
    return Com.SKIP

  partial def pZER : Parsec Com := do
    let i ← lexeme $ var
    lexeme <| skipChar '='
    lexeme <| skipChar '0'
    return Com.ZER i

  partial def pASN : Parsec Com := do
    let i1 ← lexeme $ var
    lexeme <| skipChar '='
    let i2 ← lexeme $ var
    return Com.ASN i1 i2

  partial def pINC : Parsec Com := do
    let i ← lexeme $ var
    lexeme <| skipString "+="
    lexeme <| skipChar '1'
    return Com.INC i

  partial def pSEQ : Parsec Com := do
    let P ← pSingle
    newline
    let Q ← pCom
    return Com.SEQ P Q

  partial def pFOR := do
    lexeme <| skipString "LOOP"
    let i ← lexeme <| var
    newline
    let body ← pCom
    newline
    lexeme <| skipString "END"
    return Com.FOR i body
end
