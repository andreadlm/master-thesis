import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language

namespace Compiler

open LOOP Com
open SCORE Com

def l2s (P : LOOP.Com) : SCORE.Com :=
  match P with
  | .SKIP     => SKIP
  | .ZER x    => CON x
  | .ASN x y  => if x ≠ y then
                   CON x;;
                   FOR y (INC x)
                 else SKIP
  | .INC x    => INC x
  | .SEQ P Q  => l2s P;;
                 l2s Q
  | .LOOP x P => FOR x (l2s P)

end Compiler
