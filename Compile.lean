import MasterThesis.LOOP.Parser

structure Config where
  inputFile  : String
  outputFile : String := "out.SCORE"

def usage : String :=
  "Usage: compile input_file -o <output_file>"

def configFromArgs (args : List String) : Option Config :=
  match args with
  | [iFile, "-o", oFile] => some {inputFile := iFile, outputFile := oFile}
  | [iFile]              => some {inputFile := iFile}
  | _                    => none

def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | some config =>
    try
      let inputText ← IO.FS.readFile config.inputFile
      match Lean.Parsec.run parse inputText with
      | .ok prog =>
        IO.FS.writeFile config.outputFile (toString prog)
        return UInt32.ofNat 0
      | .error e =>
        IO.eprintln s!"Error: {e}"
        return UInt32.ofNat 0
    catch e : IO.Error => do
      IO.eprintln s!"Error: {e}"
      return UInt32.ofNat 0
  | none        =>
    IO.eprintln usage
    return UInt32.ofNat 1
