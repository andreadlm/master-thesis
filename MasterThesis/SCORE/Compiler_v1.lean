import MasterThesis.SCORE.Language
import MasterThesis.LOOP.Language

namespace SCORE

open SCORE Com

def l2s (Lc : LOOP.Com) : SCORE.Com :=
  match Lc with
  | LOOP.Com.SKIP    => SKIP
  | LOOP.Com.ZER x   => CON x
  | LOOP.Com.ASN x y => if x ≠ y then
                          CON x ;;
                          FOR y (INC x)
                        else SKIP
  | LOOP.Com.INC x   => INC x
  | LOOP.Com.SEQ P Q => l2s P ;;
                        l2s Q
  | LOOP.Com.FOR x P => FOR x (l2s P)

namespace l2s

def eq_stores (σ : LOOP.Store) (τ : SCORE.Store) : Prop :=
  ∀ (x : Ident), (some (Int.ofNat (σ x)) = (τ x).head?)

infix:50 "=ₛ" => eq_stores

end l2s

end SCORE
