import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language

namespace SCORE

open SCORE Com

def l2s' (ev : Ident) (Lc: LOOP.Com) : SCORE.Com :=
  match Lc with
  | LOOP.Com.SKIP    => SKIP
  | LOOP.Com.ZER x   => CON x
  | LOOP.Com.ASN x y => FOR y (INC ev) ;;
                        CON x ;;
                        FOR ev (INC x) ;;
                        FOR x (DEC ev)
  | LOOP.Com.INC x   => INC x
  | LOOP.Com.SEQ P Q => l2s' ev P ;;
                        l2s' ev Q
  | LOOP.Com.FOR x P => FOR x (l2s' ev P)

end SCORE
