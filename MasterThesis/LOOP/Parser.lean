/-
"A LEAN-certified reversibilization of Meyer-Ritchie LOOP language".
Master thesis in computer science, University of Turin.
Author: Andrea Delmastro
-/
import Lean.Data.Parsec
import MasterThesis.LOOP.Language

/-!
# LOOP parser

This file defines a simple parser for the LOOP language, written using the standard `Parsec`
library.
The accepted syntax for a loop program is defined as follows:
$$
\begin{array}{lclcl}
    \texttt{Ident} & \ni & x, y &     & \\
    \texttt{Com}   & \ni & P, Q & ::= & \texttt{SKIP} \mid x \; \texttt{=} \; \texttt{0} \mid x \; \texttt{=} \; y \mid x \; \texttt{=} \; x \; \texttt{+} \; \texttt{1}\\
                   &     &      &     & \mid P \texttt{;} Q \mid \texttt{LOOP} \; x \; \texttt{DO} \; P \; \texttt{END}
\end{array}
$$

## References

This work is strongly based on the following resources:
* <https://jakewheat.github.io/intro_to_parsing>
* <https://wiki.haskell.org/Parsing_a_simple_imperative_language>
* <https://leanprover-community.github.io/mathlib4_docs/Lean/Data/Json/Parser.html>
-/

open Lean Parsec
open LOOP Com

/-- Parses a variable. -/
def var : Parsec String := do
    let fc ← firstChar
    let rest ← many nonFirstChar
    return ⟨fc :: rest.toList⟩
  where
    firstChar := satisfy Char.isAlpha
    nonFirstChar := satisfy <| fun c => c.isAlpha || c.isDigit || c == '_'

/-- Parses a syntactic construct followed by a sequence of blank or tab characters. -/
def lexeme {α : Type} (p : Parsec α) : Parsec α := do
  let x ← p
  let _ ← many <| satisfy fun c => c == ' ' || c == '\t'
  return x

/-- Parses a newline character. -/
def newline : Parsec Unit := do
  skipChar '\n' <|> skipString "\r\n"
  ws

mutual
  /-- Parses a program file. -/
  partial def parse : Parsec Com := do
    ws
    let prog ← pCom
    ws
    eof
    return prog

  /-- Parses one or more commands. -/
  partial def pCom : Parsec Com :=
    attempt pSEQ  <|> pSingle

  /-- Parses a single command. -/
  partial def pSingle : Parsec Com :=
    attempt pSKIP <|>
    attempt pZER  <|>
    attempt pASN  <|>
    attempt pINC  <|>
            pLOOP

  /-- Parses a SKIP command with 'SKIP' syntax. -/
  partial def pSKIP : Parsec Com := do
    lexeme <| skipString "SKIP"
    return Com.SKIP

  /-- Parses a zeroing command with 'x = 0' syntax. -/
  partial def pZER : Parsec Com := do
    let i ← lexeme $ var
    lexeme <| skipChar '='
    lexeme <| skipChar '0'
    return Com.ZER i

  /-- Parses an assignment command with 'x = y' syntax. -/
  partial def pASN : Parsec Com := do
    let i1 ← lexeme $ var
    lexeme <| skipChar '='
    let i2 ← lexeme $ var
    return Com.ASN i1 i2

  /-- Parses an increment command with 'x += 1' syntax. -/
  partial def pINC : Parsec Com := do
    let i ← lexeme $ var
    lexeme <| skipString "+="
    lexeme <| skipChar '1'
    return Com.INC i

  /-- Parses a sequential command -/
  partial def pSEQ : Parsec Com := do
    let P ← pSingle
    lexeme <| skipChar ';'
    ws
    let Q ← pCom
    return Com.SEQ P Q

  /-- Parses a LOOP command with 'LOOP x DO P END' syntax. -/
  partial def pLOOP := do
    lexeme <| skipString "LOOP"
    let i ← lexeme <| var
    lexeme <| skipString "DO"
    newline
    let body ← pCom
    newline
    lexeme <| skipString "END"
    return Com.LOOP i body
end
