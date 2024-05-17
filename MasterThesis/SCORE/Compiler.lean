import MasterThesis.SCORE.Language
import MasterThesis.SCORE.Interpreter
import MasterThesis.LOOP.Language
import MasterThesis.LOOP.Interpreter

namespace SCORE

open SCORE.com

def LOOP2SCORE (Lc : LOOP.com) : SCORE.com :=
  match Lc with
  | LOOP.com.SKIP    => SKIP
  | LOOP.com.ZER x   => CON x
  | LOOP.com.ASN x y => CON x ;;
                        FOR y (INC x)
  | LOOP.com.INC x   => INC x
  | LOOP.com.SEQ P Q => LOOP2SCORE P ;;
                        LOOP2SCORE Q

  | LOOP.com.FOR x P => FOR x (LOOP2SCORE P)

namespace LOOP2SCORE

def eqStores (σ : LOOP.store) (τ : SCORE.store) : Prop :=
  ∀ (x : ident), σ x = (τ x).head!

infix:100 "=ₛ" => eqStores

theorem soundness : ∀ (Lc : LOOP.com) (σ : LOOP.store) (τ : SCORE.store), σ =ₛ τ → (LOOP.eval Lc σ) =ₛ (SCORE.eval (LOOP2SCORE Lc) τ) :=
  sorry

end LOOP2SCORE

end SCORE
