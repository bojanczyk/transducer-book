/-
General-purpose additions to Mathlib's `Primrec` API for lists.

Nothing in this file is about transducers.  It supplies the list operations that Mathlib's
`Mathlib/Computability/Primrec/List.lean` does not cover but that any concrete procedure on lists
needs: `List.filter`, `List.drop`, `List.take`, membership, and the prefix test on lists of natural
numbers.  The companion file `RequestProject/Common/PrimrecArith.lean` does the same for the
arithmetic of `ℤ` and `ℚ`.
-/
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.TakeWhile

namespace Primrec

variable {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]

/-! ## Filtering -/

omit [Primcodable α] in
private lemma filter_eq_foldr (p : α → Bool) (l : List α) :
    l.filter p = l.foldr (fun a m => if p a then a :: m else m) [] := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.filter_cons]; split <;> simp_all

/-- Filtering a list with a primitive recursive predicate is primitive recursive. -/
theorem list_filter {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).filter (p a) := by
  have h : Primrec fun a => (f a).foldr (fun b m => if p a b then b :: m else m) [] := by
    refine Primrec.list_foldr (f := f) (g := fun _ => ([] : List β))
      (h := fun (a : α) (x : β × List β) => if p a x.1 then x.1 :: x.2 else x.2)
      hf (const ([] : List β)) ?_
    have hcond : Primrec fun x : α × β × List β =>
        bif p x.1 x.2.1 then x.2.1 :: x.2.2 else x.2.2 :=
      Primrec.cond (hp.comp fst (fst.comp snd)) (list_cons.comp (fst.comp snd) (snd.comp snd))
        (snd.comp snd)
    exact hcond.to₂.of_eq fun a x => by cases hpx : p a x.1 <;> simp
  exact h.of_eq fun a => (filter_eq_foldr (p a) (f a)).symm

/-! ## Dropping and taking -/

/-- Dropping a prefix of given length is primitive recursive. -/
theorem list_drop : Primrec₂ (fun (l : List α) (n : ℕ) => l.drop n) := by
  have h := Primrec.nat_rec (f := fun l : List α => l)
    (g := fun (_ : List α) (p : ℕ × List α) => p.2.tail)
    (Primrec.id (α := List α)) ((list_tail.comp (snd.comp snd)).to₂)
  refine h.of_eq fun l n => ?_
  induction n with
  | zero => rfl
  | succ n ih => rw [List.drop_add_one_eq_tail_drop, ← ih]

omit [Primcodable α] in
private lemma take_eq_reverse_drop (l : List α) (n : ℕ) :
    l.take n = (l.reverse.drop (l.length - n)).reverse := by
  simp only [List.reverse_drop, List.reverse_reverse, List.length_reverse,
    List.take_eq_take_iff]
  omega

/-- Taking a prefix of given length is primitive recursive. -/
theorem list_take : Primrec₂ (fun (l : List α) (n : ℕ) => l.take n) := by
  have h : Primrec₂ fun (l : List α) (n : ℕ) =>
      (l.reverse.drop (l.length - n)).reverse :=
    (list_reverse.comp (list_drop.comp (list_reverse.comp fst)
      (Primrec.nat_sub.comp (list_length.comp fst) snd))).to₂
  exact h.of_eq fun l n => (take_eq_reverse_drop l n).symm

/-! ## Membership -/

/-- Membership in a list is a primitive recursive relation. -/
theorem list_mem [DecidableEq α] : PrimrecRel (fun (a : α) (l : List α) => a ∈ l) := by
  have h : PrimrecRel (fun (l : List α) (a : α) => ∃ b ∈ l, b = a) :=
    PrimrecRel.exists_mem_list (R := fun a b : α => a = b) Primrec.eq
  have h' : PrimrecRel (fun (a : α) (l : List α) => ∃ b ∈ l, b = a) :=
    PrimrecRel.comp h snd fst
  exact h'.of_eq fun a l => by simp

/-! ## The prefix test -/

private lemma isPrefixOf_eq_decide (l₁ l₂ : List ℕ) :
    l₁.isPrefixOf l₂ = decide (l₁ = l₂.take l₁.length) := by
  rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, decide_eq_true_eq, List.prefix_iff_eq_take]

/-- The prefix test on lists of natural numbers is primitive recursive. -/
theorem list_isPrefixOf : Primrec₂ (fun (l₁ l₂ : List ℕ) => l₁.isPrefixOf l₂) := by
  have h : Primrec₂ fun (l₁ l₂ : List ℕ) => decide (l₁ = l₂.take l₁.length) :=
    (PrimrecRel.comp (Primrec.eq (α := List ℕ)) fst
      (list_take.comp snd (list_length.comp fst))).decide.to₂
  exact h.of_eq fun l₁ l₂ => (isPrefixOf_eq_decide l₁ l₂).symm

end Primrec
