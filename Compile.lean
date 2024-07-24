/- References
https://jakewheat.github.io/intro_to_parsing/
https://wiki.haskell.org/Parsing_a_simple_imperative_language
https://leanprover-community.github.io/mathlib4_docs/Lean/Data/Json/Parser.html
-/

import MasterThesis.LOOP.Parser

def main (args : List String) : IO UInt32  :=
  match args with
  | [inputFile, outputFile] => do
    try
      let inputText ← IO.FS.readFile inputFile
      match Lean.Parsec.run parse inputText with
      | .ok prog => IO.FS.writeFile outputFile (toString prog)
      | .error e => IO.eprintln s!"Error: {e}"
      return 0
    catch e : IO.Error => do
      IO.eprintln s!"Error: {e}"
      return 1
  | _ => do
    IO.eprintln s!"Error: expected two arguments, got {args.length}"
    return 1
