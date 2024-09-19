import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language

open LOOP Com
open SCORE Com

def l2s' (ev : Ident) (P : LOOP.Com) : SCORE.Com :=
  CON ev;;
  match P with
  | .SKIP     => SKIP
  | .ZER x    => CON x
  | .ASN x y  => FOR y (INC ev);;
                 CON x;;
                 FOR ev (INC x);;
                 FOR x (DEC ev)
  | .INC x    => INC x
  | .SEQ P Q  => l2s' ev P;;
                 l2s' ev Q
  | .LOOP x P => FOR x (l2s' ev P)
