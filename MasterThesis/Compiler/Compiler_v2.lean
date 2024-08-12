import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language

def l2s' (ev : Ident) (P : LOOP.Com) : SCORE.Com :=
  match P with
  | LOOP.Com.SKIP    => SCORE.Com.SKIP
  | LOOP.Com.ZER x   => SCORE.Com.CON x
  | LOOP.Com.ASN x y => SCORE.Com.FOR y (SCORE.Com.INC ev);;
                        SCORE.Com.CON x;;
                        SCORE.Com.FOR ev (SCORE.Com.INC x);;
                        SCORE.Com.FOR x (SCORE.Com.DEC ev)
  | LOOP.Com.INC x   => SCORE.Com.INC x
  | LOOP.Com.SEQ P Q => l2s' ev P;;
                        l2s' ev Q
  | LOOP.Com.FOR x P => SCORE.Com.FOR x (l2s' ev P)
