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
  ∀ (x : ident), σ x = List.head! (τ x)

infix:100 "=ₛ" => eqStores

theorem soundness (LP : LOOP.com) (σ : LOOP.store) (τ : SCORE.store) : σ =ₛ τ → (LOOP.eval LP σ) =ₛ (SCORE.eval (LOOP2SCORE LP) τ) := by
  intros
  induction LP with
  | SKIP =>
    simp[LOOP.eval, LOOP2SCORE, SCORE.eval]
    assumption
  | ZER x =>
    simp[LOOP.eval, LOOP2SCORE, SCORE.eval]
    intro y
    cases eq_or_ne x y with
    | inl =>
      simp[List.head!, store.update_same ‹x = y›, LOOP.store.update_same ‹x = y›]
    | inr =>
      simp[store.update_other ‹x ≠ y›, LOOP.store.update_other ‹x ≠ y›]
      apply ‹σ =ₛ τ› y
  | ASN x y => sorry
  | INC x =>
    simp[LOOP.eval, LOOP2SCORE, SCORE.eval]
    intro y
    cases eq_or_ne x y with
    | inl =>
      simp[List.head!, store.update_same ‹x = y›, LOOP.store.update_same ‹x = y›]
      apply ‹σ =ₛ τ› x
    | inr =>
      simp[List.head!, store.update_other ‹x ≠ y›, LOOP.store.update_other ‹x ≠ y›]
      apply ‹σ =ₛ τ› y
  | SEQ LQ LR => sorry
  | FOR x LQ => sorry

end LOOP2SCORE

end SCORE
