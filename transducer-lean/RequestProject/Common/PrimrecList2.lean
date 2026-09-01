/-
Further additions to Mathlib's `Primrec` API for lists: searching a list, testing all its
elements, and enumerating its sublists.

Like `RequestProject/Common/PrimrecList.lean`, nothing here is about transducers.  These are the
operations needed to show that the construction of the effective Uniformisation Lemma
(`RequestProject/Exercises/RatSectionPrimrec.lean`) is primitive recursive.
-/
import RequestProject.Common.PrimrecList
import Mathlib.Data.List.Sublists

namespace Primrec

variable {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]

/-- Searching a list for the first element satisfying a primitive recursive predicate is
primitive recursive. -/
theorem list_find? {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) := by
  have h : Primrec fun a => List.rec (motive := fun _ => Option β) (none : Option β)
      (fun b _ IH => if p a b then some b else IH) (f a) := by
    refine Primrec.list_rec hf (const none)
      (h := fun (a : α) (x : β × List β × Option β) =>
        if p a x.1 then some x.1 else x.2.2) ?_
    have hcond : Primrec fun q : α × (β × List β × Option β) =>
        bif p q.1 q.2.1 then some q.2.1 else q.2.2.2 :=
      Primrec.cond (hp.comp fst (fst.comp snd)) (option_some.comp (fst.comp snd))
        (snd.comp (snd.comp snd))
    exact hcond.to₂.of_eq fun a x => by cases hpx : p a x.1 <;> simp
  refine h.of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b l ih => rw [List.find?_cons]; split <;> simp_all

/-- Testing that all the elements of a list satisfy a primitive recursive predicate is primitive
recursive. -/
theorem list_all {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) := by
  have hnot : Primrec₂ fun (a : α) (b : β) => !p a b :=
    ((Primrec.dom_bool not).comp hp).to₂
  have hfil : Primrec fun a => (f a).filter (fun b => !p a b) := list_filter hf hnot
  have h : Primrec fun a => decide (((f a).filter (fun b => !p a b)).length = 0) :=
    (PrimrecRel.comp Primrec.eq (list_length.comp hfil) (const 0)).decide
  refine h.of_eq fun a => ?_
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.length_eq_zero_iff, List.filter_eq_nil_iff,
    List.all_eq_true]
  constructor
  · intro hh b hb; simpa using hh b hb
  · intro hh b hb; simpa using hh b hb

/-- Enumerating the sublists of a list is primitive recursive. -/
theorem list_sublists : Primrec (@List.sublists α) := by
  have hH : Primrec₂ (fun (_ : List α) (x : α × List α × List (List α)) =>
      x.2.2.flatMap (fun y => [y, x.1 :: y])) := by
    have h1 : Primrec fun q : List α × (α × List α × List (List α)) => q.2.2.2 :=
      snd.comp (snd.comp snd)
    have h2 : Primrec₂ fun (q : List α × (α × List α × List (List α))) (y : List α) =>
        [y, q.2.1 :: y] := by
      have h3 : Primrec fun z : (List α × (α × List α × List (List α))) × List α =>
          z.2 :: (z.1.2.1 :: z.2) :: ([] : List (List α)) :=
        list_cons.comp snd (list_cons.comp (list_cons.comp (fst.comp (snd.comp fst)) snd)
          (const []))
      exact h3
    exact (Primrec.list_flatMap h1 h2).to₂
  have h : Primrec fun l : List α =>
      List.rec (motive := fun _ => List (List α)) ([[]] : List (List α))
        (fun a _ IH => IH.flatMap (fun x => [x, a :: x])) l :=
    Primrec.list_rec Primrec.id (const [[]]) hH
  refine h.of_eq fun l => ?_
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.sublists_cons, ← ih]; simp [List.flatMap]

end Primrec
