import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language

namespace Compiler

open LOOP Com
open SCORE Com

def l2s (Lc : LOOP.Com) : SCORE.Com :=
  match Lc with
  | .SKIP    => SKIP
  | .ZER x   => CON x
  | .ASN x y => if x ≠ y then
                  CON x ;;
                  FOR y (INC x)
                else SKIP
  | .INC x   => INC x
  | .SEQ P Q => l2s P ;;
                l2s Q
  | .FOR x P => FOR x (l2s P)

end Compiler
