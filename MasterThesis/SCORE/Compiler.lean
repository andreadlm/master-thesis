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
  | LOOP.com.ASN x y => if x ≠ y then
                          CON x ;;
                          FOR y (INC x)
                        else SKIP
  | LOOP.com.INC x   => INC x
  | LOOP.com.SEQ P Q => L2S P ;;
                        L2S Q
  | LOOP.com.FOR x P => FOR x (L2S P)

namespace L2S

def eq_stores (σ : LOOP.store) (τ : SCORE.store) : Prop :=
  ∀ (x : ident), Int.ofNat (σ x) = (τ x).head!

infix:100 "=ₛ" => eq_stores

lemma eq_stores_update {σ : LOOP.store} {τ : SCORE.store} : ∀ (x : ident) (v : ℕ), σ =ₛ τ → ([x ↦ v]σ) =ₛ ([x ↦ (Int.ofNat v) :: τ x]τ) := by
  intros x v _ y
  cases eq_or_ne x y with
  | inl /- x = y -/ => simp[List.head!, ‹x = y›]
  | inr /- x ≠ y -/ => simp[‹x ≠ y›]; exact ‹σ =ₛ τ› y

lemma eq_stores_INC {σ : LOOP.store} {τ : SCORE.store} {x : ident} {v : ℕ}: ([x ↦ v]σ) =ₛ τ →  ([x ↦ v + 1]σ) =ₛ SCORE.eval (INC x) τ := by
  intros _ y
  cases eq_or_ne x y with
  | inl /- x = y -/ => -- Migliorare
    simp only [SCORE.eval, ←‹x = y›, ←(‹([x ↦ v]σ) =ₛ τ› x)]
    simp [List.head!]
  | inr /- x ≠ y -/ => have := ‹([x ↦ v]σ) =ₛ τ› y; simpa [SCORE.eval, ‹x ≠ y›]


theorem soundness {σ : LOOP.store} {τ : SCORE.store} (LP : LOOP.com) : σ =ₛ τ → (LOOP.eval LP σ) =ₛ (SCORE.eval (L2S LP) τ) := by
  intro
  induction LP generalizing σ τ with
  | SKIP => simpa only [LOOP.eval, L2S, SCORE.eval]
  | ZER x =>
    simp only [LOOP.eval, L2S, SCORE.eval]
    intro y
    cases eq_or_ne x y with
    | inl /- x = y -/ => simp [List.head!, ‹x = y›]
    | inr /- x ≠ y -/ => have := ‹σ =ₛ τ› y; simpa [‹x ≠ y›, ‹σ =ₛ τ› y]
  | ASN x y =>
    simp only [LOOP.eval, L2S, SCORE.eval]
    cases eq_or_ne x y with
    | inl /- x = y -/ => simpa [List.head!, SCORE.eval, LOOP.store.update_no_update, ‹x = y›]
    | inr /- x ≠ y -/ => -- Migliorare
      simp [‹x ≠ y›]
      repeat rewrite [SCORE.eval]
      simp [‹x ≠ y›, ←(‹σ =ₛ τ› y)]
      induction (σ y) generalizing σ τ with
      | zero      => have := eq_stores_update x 0 ‹σ=ₛτ›; simpa
      | succ m ih => have := eq_stores_INC (ih ‹σ =ₛ τ›); simpa [Nat.add_comm m 1, Function.iterate_add_apply]
  | INC x =>
    simp only [LOOP.eval, L2S, SCORE.eval]
    intro y
    cases eq_or_ne x y with
    | inl /- x = y -/ => have := ‹σ =ₛ τ› y; simpa [List.head!, ‹x = y›]
    | inr /- x ≠ y -/ => have := ‹σ =ₛ τ› y; simpa [‹x ≠ y›]
  | SEQ LQ LR ih₁ ih₂ => have := ih₂ (ih₁ ‹σ =ₛ τ›); simpa only [LOOP.eval, L2S, SCORE.eval]
  | FOR x LQ ih₁ =>
    simp only [LOOP.eval, L2S, SCORE.eval, ←(‹σ =ₛ τ› x)]
    induction (σ x) generalizing σ τ with
    | zero       => have := ‹σ =ₛ τ›; simpa
    | succ _ ih₂ => exact ih₂ (ih₁ ‹σ =ₛ τ›)
end L2S

end SCORE
