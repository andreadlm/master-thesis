import MasterThesis.SCORE.Language
import MasterThesis.SCORE.Interpreter
import MasterThesis.LOOP.Language
import MasterThesis.LOOP.Interpreter

set_option pp.notation true

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
  ∀ (x : ident), Int.ofNat (σ x) = (τ x).head!

infix:100 "=ₛ" => eqStores

namespace Function

def Iterate.rec_pair {f : α → α} {g : β → β} {a : α} {b : β} (p : α → β → Sort*) (h : ∀ a b, p a b → p (f a) (g b)) (hab : p a b) (n : ℕ) :
  p (f^[n] a) (g^[n] b) :=
  match n with
  | 0 => hab
  | (m + 1) => Iterate.rec_pair p h (h a b hab) m

end Function

theorem soundness (LP : LOOP.com) (σ : LOOP.store) (τ : SCORE.store) : σ =ₛ τ → (LOOP.eval LP σ) =ₛ (SCORE.eval (L2S LP) τ) := by
  intro eqStores
  induction LP generalizing σ τ <;> rewrite[LOOP.eval, L2S, SCORE.eval]
  case SKIP => assumption
  case ZER x =>
    intro y
    cases eq_or_ne x y with
    | inl =>
      rewrite[List.head!]
      simp[store.update_same ‹x = y›]
      rewrite[LOOP.store.update_same ‹x = y›]
      rfl
    | inr =>
      rewrite[store.update_other ‹x ≠ y›, LOOP.store.update_other ‹x ≠ y›]
      apply ‹σ =ₛ τ› y
  case INC x =>
    intro y
    cases eq_or_ne x y with
    | inl =>
      rewrite[List.head!]
      simp[store.update_same ‹x = y›]
      rewrite[LOOP.store.update_same ‹x = y›]
      simp -- Chiamata esplicita?
      apply ‹σ =ₛ τ› x
    | inr =>
      rewrite[store.update_other ‹x ≠ y›, LOOP.store.update_other ‹x ≠ y›]
      apply ‹σ =ₛ τ› y
  case SEQ LQ LR ih₁ ih₂ =>
     apply ih₂
     apply ih₁
     assumption
  case FOR x LQ ih₁ =>
    simp[←(‹σ =ₛ τ› x)]
    induction (σ x) generalizing σ τ <;> simp
    case zero => assumption
    case succ m ih₂ =>
      apply ih₂
      apply ih₁
      assumption
  case ASN x y => sorry
end L2S

end SCORE
