import Mathlib.Data.Prod.Basic

import MasterThesis.Commons

namespace SCORE

def store : Type := (ident → List Int) × Bool

def error (s : store) : Prop :=
  match s with
  | (_, true ) => False
  | (_, false) => True

lemma not_error_iff_true {s : store} : ¬error s ↔ ∃ σ, s = (σ, true) := by
  constructor
  case mp =>
    intro
    match s with
    | (σ, true ) => exists σ
    | (σ, false) => simp only [error, not_true_eq_false] at ‹¬error (σ, false)›
  case mpr =>
    intro
    cases ‹∃ σ, s = (σ, true)› with
    | intro σ => simp only [‹s = (σ, true)›, error, not_false_eq_true]

lemma error_iff_false {s : store} : error s ↔ ∃ σ, s = (σ, false) := by
  constructor
  case mp  =>
    intro
    match s with
    | (σ, true ) => simp only [error] at ‹error (σ, true)›
    | (σ, false) => exists σ
  case mpr =>
    intro
    cases ‹∃ σ, s = (σ, false)› with
    | intro σ => simp only [‹s = (σ, false)›, error]

namespace store

def emp : store := (fun _ => [], true)

def update (x : ident) (l : List Int) (s : store) : store :=
  match s with
  | (σ, true )  => (fun (y : ident) => if x = y then l else (σ y), true)
  | (σ, false)  => (σ, false)

-- TODO: Migliorabile?
notation:100 "[" x:100 " ↦ " l:100 "]" s:100 => update x l s
notation:100 "[" x:100 " ↦ " l:100 "]"       => [x ↦ l] emp

#eval (["z" ↦ [3]] ["y" ↦ [2]] ["x" ↦ [1]]).fst "x"

@[simp]
lemma update_same {s : store} {x y : ident} {l : List Int} : ¬error s → x = y → (store.update x l s).fst y = l := by
  intros
  cases (not_error_iff_true.mp ‹¬error s›) with
  | intro σ => simp only [update, ‹s = (σ, true)›, if_pos ‹x = y›]

@[simp]
lemma update_other {s : store} {x y : ident} {l : List Int} : ¬error s → x ≠ y → (store.update x l s).fst y = s.fst y := by
  intros
  cases (not_error_iff_true.mp ‹¬error s›) with
  | intro σ => simp only [update, ‹s = (σ, true)›, if_neg ‹x ≠ y›]

lemma update_shrink {s : store} {x : ident} {l₁ l₂ : List Int} : ¬error s → (store.update x l₂ (store.update x l₁ s)) = store.update x l₂ s := by
  intro
  cases (not_error_iff_true.mp ‹¬error s›) with
  | intro σ =>
    rw [‹s = (σ, true)›]
    simp only [update]
    apply Prod.eq_iff_fst_eq_snd_eq.mpr
    constructor
    case intro.left  =>
      simp only [Prod.fst]
      funext y
      cases eq_or_ne x y with
      | inl /- x = y -/ => simp only [if_pos ‹x = y›]
      | inr /- x ≠ y -/ => simp only [if_neg ‹x ≠ y›]
    case intro.right => simp only [Prod.snd]

lemma update_unchanged {s : store} {x : ident} : ¬error s → s = store.update x (s.fst x) s := by
  intro
  cases (not_error_iff_true.mp ‹¬error s›) with
  | intro σ =>
    rw [‹s = (σ, true)›]
    simp only [update]
    apply Prod.eq_iff_fst_eq_snd_eq.mpr
    constructor
    case intro.left  =>
      simp only [Prod.fst]
      funext y
      cases eq_or_ne x y with
      | inl /- x = y -/ => simp only [if_pos ‹x = y›]; rw [‹x = y›]
      | inr /- x ≠ y -/ => simp only [if_neg ‹x ≠ y›]
    case intro.right => simp only [Prod.snd]

lemma update_unchanged_cons {s : store} {x : ident} {v : Int} : (s.fst x).head? = some v → s = store.update x (v :: (s.fst x).tail) s := by
  sorry

end store

inductive com : Type
| SKIP : com
| CON  : ident → com
| NOC  : ident → com
| DEC  : ident → com
| INC  : ident → com
| SEQ  : com → com → com
| FOR  : ident → com → com
deriving Repr

open com

infixl:80 ";;" => SEQ

def inv (P : com) : com :=
  match P with
  | SKIP    => SKIP
  | CON x   => NOC x
  | NOC x   => CON x
  | DEC x   => INC x
  | INC x   => DEC x
  | SEQ Q R => SEQ (inv R) (inv Q)
  | FOR x Q => FOR x (inv Q)

theorem inv_inv (P : com) : (inv (inv P)) = P := by
  induction  P
  case SKIP        => simp[inv]
  case CON         => simp[inv]
  case NOC         => simp[inv]
  case DEC         => simp[inv]
  case INC         => simp[inv]
  case SEQ ih₁ ih₂ => simp[inv, ih₁, ih₂]
  case FOR ih      => simp[inv, ih]

end SCORE
