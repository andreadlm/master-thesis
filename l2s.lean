import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Parser
import MasterThesis.Compiler.Compiler_v1

structure Config where
  inputFile  : String := ""
  outputFile : String := ""
  printHelp  : Bool   := false

def usage : String :=
"Usage: compile [options] file
Options:
  --help    Display this information
  -o <file> Place the output into <file>"

def configFromArgs (args : List String) : Option Config :=
  match args with
  | ["--help"]           => some {printHelp := true}
  | ["-o", oFile, iFile] => some {inputFile := iFile, outputFile := oFile}
  | [iFile]              => some {inputFile := iFile, outputFile := "out.score"}
  | _                    => none

def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | some config =>
    if config.printHelp == true then
      IO.println usage
      return UInt32.ofNat 0
    else
      try
        let inputText ← IO.FS.readFile config.inputFile
        match Lean.Parsec.run parse inputText with
        | .ok prog =>
          IO.FS.writeFile config.outputFile (toString <| Compiler.l2s prog)
          return UInt32.ofNat 0
        | .error e =>
          IO.eprintln s!"Error: {e}"
          return UInt32.ofNat 1
      catch e : IO.Error => do
        IO.eprintln s!"Error: {e}"
        return UInt32.ofNat 1
  | none =>
    IO.eprintln usage
    return UInt32.ofNat 1
