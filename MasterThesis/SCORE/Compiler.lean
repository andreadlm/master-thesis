import MasterThesis.SCORE.Language
import MasterThesis.SCORE.Interpreter
import MasterThesis.LOOP.Language
import MasterThesis.LOOP.Interpreter

namespace SCORE

open SCORE.com

def L2S (Lc : LOOP.com) : SCORE.com :=
  match Lc with
  | LOOP.com.SKIP    => SKIP
  | LOOP.com.ZER x   => CON x
  | LOOP.com.ASN x y => CON x ;;
                        FOR y (INC x)
  | LOOP.com.INC x   => INC x
  | LOOP.com.SEQ P Q => L2S P ;;
                        L2S Q

  | LOOP.com.FOR x P => FOR x (L2S P)

namespace L2S

def eqStores (σ : LOOP.store) (τ : SCORE.store) : Prop :=
  ∀ (x : ident), σ x = List.head! (τ x)

infix:100 "=ₛ" => eqStores

theorem soundness (LP : LOOP.com) (σ : LOOP.store) (τ : SCORE.store) : σ =ₛ τ → (LOOP.eval LP σ) =ₛ (SCORE.eval (L2S LP) τ) := by
  intros
  induction LP generalizing σ τ with
  | SKIP =>
    simp[LOOP.eval, L2S, SCORE.eval]
    assumption
  | ZER x =>
    simp[LOOP.eval, L2S, SCORE.eval]
    intro y
    cases eq_or_ne x y with
    | inl =>
      simp[List.head!, store.update_same ‹x = y›, LOOP.store.update_same ‹x = y›]
    | inr =>
      simp[store.update_other ‹x ≠ y›, LOOP.store.update_other ‹x ≠ y›]
      apply ‹σ =ₛ τ› y
  | ASN x y => sorry
  | INC x =>
    simp[LOOP.eval, L2S, SCORE.eval]
    intro y
    cases eq_or_ne x y with
    | inl =>
      simp[List.head!, store.update_same ‹x = y›, LOOP.store.update_same ‹x = y›]
      apply ‹σ =ₛ τ› x
    | inr =>
      simp[List.head!, store.update_other ‹x ≠ y›, LOOP.store.update_other ‹x ≠ y›]
      apply ‹σ =ₛ τ› y
  | SEQ LQ LR ih₁ ih₂ =>
     simp[LOOP.eval, L2S, SCORE.eval]
     apply ih₂ (LOOP.eval LQ σ) (eval (L2S LQ) τ) (ih₁ σ τ ‹σ =ₛ τ›)
  | FOR x LQ => sorry

end L2S

end SCORE
