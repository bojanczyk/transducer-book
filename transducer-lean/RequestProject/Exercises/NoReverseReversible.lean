/-
Exercise `exer:no-reverse-reversible` of *Transducers* (M. Bojańczyk): in the list of atomic
functions of Theorem `thm:rational-primes`, the reversal of a reversible Mealy machine is not
needed.

The list of Theorem `thm:rational-primes` has four items -- the prime (reversible or flip-flop)
Mealy machines, their right-to-left variants, the string homomorphisms and the function `w ↦ w#`.
Here `Transducers.Exercises.PrimeRatNoRevRevFam` is the same list with the right-to-left
*reversible* machines dropped from the second item, and the exercise says that the compositions of
this shorter list are still exactly the rational functions.

The author's solution, which is the one followed here.  To implement a right-to-left reversible
Mealy machine with states `Q`:

* append the separator `#` (the fourth prime);
* run an ordinary left-to-right reversible Mealy machine whose states are the permutations of `Q`,
  labelling every position with the state transformation of the prefix that leads up to it, and
  the separator with the transformation of the whole input;
* run a right-to-left flip-flop machine, which copies the label of the separator -- the
  transformation of the whole input -- to every position;
* by cancellation in the group of permutations of `Q`, the transformation of the suffix after a
  position is the transformation of the whole input divided by that of the prefix up to and
  including it; a homomorphism recovers the wanted output letter from it, and erases the
  separator.

The composition order deserves a word.  `Transducers.Mealy.trans` composes on the left, so the
product `p a₁ * ⋯ * p aᵢ` of the permutations of the letters of a prefix, `rtlProd` below, is the
state transformation of the *reverse* of that prefix, which is exactly what a right-to-left
machine applies to it.
-/
import RequestProject.PartB.RationalStatements
import RequestProject.PartB.PrimeRat

namespace Transducers.Exercises

open Transducers

/-- The prime rational functions of Theorem `thm:rational-primes` with the right-to-left
reversible Mealy machines dropped: prime (reversible or flip-flop) Mealy machines, the
right-to-left *flip-flop* Mealy machines, string homomorphisms, and the function `w ↦ w#`
appending a fresh separator. -/
def PrimeRatNoRevRevFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  PrimeMealyFam A B f ∨
  IsFlipFlopMealy (fun w => (f w.reverse).reverse) ∨
  (∃ φ : A → List B, f = homOf φ) ∨
  (∃ e : Option A ≃ B, f = fun w => w.map (fun a => e (some a)) ++ [e none])

/-! ### Two elementary facts about homomorphisms -/

lemma hom_cons {A B : Type} (φ : A → List B) (a : A) (w : List A) :
    homOf φ (a :: w) = φ a ++ homOf φ w := by simp [homOf]

lemma hom_append {A B : Type} (φ : A → List B) (u v : List A) :
    homOf φ (u ++ v) = homOf φ u ++ homOf φ v := by simp [homOf]

/-! ### The right-to-left flip-flop machine

It does not depend on the machine that is being implemented: it reads a letter together with a
permutation, and it remembers the permutation carried by the separator. -/

/-- The right-to-left flip-flop machine that copies the label of the separator to every
position. -/
def bcastMealy (A : Type) (Q : Type) : Mealy (Option A × Equiv.Perm Q)
    (Option A × Equiv.Perm Q × Equiv.Perm Q) (Equiv.Perm Q) where
  init := 1
  step := fun G x => (match x.1 with | none => x.2 | some _ => G, (x.1, x.2, G))

lemma bcastMealy_flipFlop (A Q : Type) : (bcastMealy A Q).FlipFlop := by
  rintro ⟨x, P⟩
  cases x with
  | none => exact Or.inr ⟨P, fun _ => rfl⟩
  | some a => exact Or.inl rfl

/-- Reading right to left, the flip-flop machine leaves its state unchanged on the letters that
are not the separator. -/
lemma bcastMealy_run_of_isSome {A Q : Type} (z : List (Option A × Equiv.Perm Q))
    (hz : ∀ y ∈ z, y.1.isSome) (G : Equiv.Perm Q) :
    (bcastMealy A Q).run G z = z.map (fun y => (y.1, y.2, G)) := by
  induction z generalizing G with
  | nil => rfl
  | cons y z ih =>
      obtain ⟨a, ha⟩ : ∃ a, y.1 = some a := Option.isSome_iff_exists.1 (hz y (by simp))
      have hstep : (bcastMealy A Q).step G y = (G, (y.1, y.2, G)) := by
        show ((match y.1 with | none => y.2 | some _ => G), _) = _
        rw [ha]
      rw [Mealy.run_cons, hstep, ih (fun t ht => hz t (by simp [ht]))]
      simp

section RtlReversible

variable {A B Q : Type} (M : Mealy A B Q) (hrev : M.Reversible)

/-- The permutation of the states induced by a letter, for a reversible Mealy machine. -/
noncomputable def rtlPerm (a : A) : Equiv.Perm Q := Equiv.ofBijective (M.letterTrans a) (hrev a)

@[simp] lemma rtlPerm_apply (a : A) (q : Q) : rtlPerm M hrev a q = M.letterTrans a q := rfl

/-- The permutation of a letter of the extended alphabet; the separator does nothing. -/
noncomputable def rtlPermOpt : Option A → Equiv.Perm Q
  | none => 1
  | some a => rtlPerm M hrev a

@[simp] lemma rtlPermOpt_none : rtlPermOpt M hrev none = 1 := rfl

@[simp] lemma rtlPermOpt_some (a : A) : rtlPermOpt M hrev (some a) = rtlPerm M hrev a := rfl

/-- The product of the permutations of the letters of a string, in the order in which they are
written.  Applied to a state, it is the state transformation of the *reverse* of the string. -/
noncomputable def rtlProd (w : List A) : Equiv.Perm Q := (w.map (rtlPerm M hrev)).prod

@[simp] lemma rtlProd_nil : rtlProd M hrev [] = 1 := rfl

@[simp] lemma rtlProd_cons (a : A) (w : List A) :
    rtlProd M hrev (a :: w) = rtlPerm M hrev a * rtlProd M hrev w := by
  simp [rtlProd]

lemma rtlProd_apply (w : List A) (q : Q) : rtlProd M hrev w q = M.trans w.reverse q := by
  induction w generalizing q with
  | nil => simp
  | cons a w ih =>
      rw [rtlProd_cons, Equiv.Perm.mul_apply, ih, rtlPerm_apply, List.reverse_cons,
        Mealy.trans_append]
      rfl

/-! ### The left-to-right reversible machine -/

/-- The left-to-right reversible Mealy machine that labels every position with the product of the
permutations of the letters before it. -/
noncomputable def labMealy : Mealy (Option A) (Option A × Equiv.Perm Q) (Equiv.Perm Q) where
  init := 1
  step := fun P x => (P * rtlPermOpt M hrev x, (x, P))

lemma labMealy_reversible : (labMealy M hrev).Reversible :=
  fun x => Group.mulRight_bijective (rtlPermOpt M hrev x)

/-- The labelling computed by `labMealy`, started in an arbitrary state. -/
noncomputable def labList : Equiv.Perm Q → List (Option A) → List (Option A × Equiv.Perm Q)
  | _, [] => []
  | P, x :: u => (x, P) :: labList (P * rtlPermOpt M hrev x) u

lemma labMealy_run (u : List (Option A)) (P : Equiv.Perm Q) :
    (labMealy M hrev).run P u = labList M hrev P u := by
  induction u generalizing P with
  | nil => rfl
  | cons x u ih => simpa [labMealy, labList] using ih _

/-- The labelling of a string followed by the separator: the separator carries the product over
the whole string. -/
lemma labList_append_sep (w : List A) (P : Equiv.Perm Q) :
    labList M hrev P (w.map some ++ [none]) =
      (labList M hrev P (w.map some)) ++ [(none, P * rtlProd M hrev w)] := by
  induction w generalizing P with
  | nil => simp [labList]
  | cons a w ih =>
      have h := ih (P * rtlPerm M hrev a)
      simp only [List.map_cons, List.cons_append, labList, rtlPermOpt, h, rtlProd_cons,
        mul_assoc]

lemma labList_isSome (w : List A) (P : Equiv.Perm Q) :
    ∀ y ∈ labList M hrev P (w.map some), y.1.isSome := by
  induction w generalizing P with
  | nil => simp [labList]
  | cons a w ih =>
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · simp
      · exact ih _ y hy

/-! ### The homomorphism -/

/-- The homomorphism that recovers the output of the right-to-left Mealy machine: from the letter
`a`, the transformation `P` of the prefix before it and the transformation `G` of the whole input,
the state after the suffix that follows `a` is `(P * p a)⁻¹ * G`. -/
noncomputable def outHom : Option A × Equiv.Perm Q × Equiv.Perm Q → List B
  | (none, _, _) => []
  | (some a, P, G) => [(M.step (((P * rtlPerm M hrev a)⁻¹ * G) M.init) a).2]

/-- The output of the homomorphism on a labelled string: this is where cancellation in the group
of permutations of the states happens. -/
lemma homOf_outHom_labList (w : List A) (P : Equiv.Perm Q) :
    homOf (outHom M hrev)
        ((labList M hrev P (w.map some)).map
          (fun y => (y.1, y.2, P * rtlProd M hrev w))) =
      (M.eval w.reverse).reverse := by
  induction w generalizing P with
  | nil => simp [labList, homOf, Mealy.eval]
  | cons a w ih =>
      have hP : P * rtlProd M hrev (a :: w) = (P * rtlPerm M hrev a) * rtlProd M hrev w := by
        rw [rtlProd_cons, mul_assoc]
      have hhead : outHom M hrev
          ((some a : Option A), P, P * rtlProd M hrev (a :: w)) =
            [(M.step (M.trans w.reverse M.init) a).2] := by
        show [(M.step (((P * rtlPerm M hrev a)⁻¹ * (P * rtlProd M hrev (a :: w))) M.init) a).2] = _
        rw [hP]
        simp [← mul_assoc, rtlProd_apply]
      have htail := ih (P * rtlPerm M hrev a)
      rw [List.map_cons, labList, List.map_cons, hom_cons, hhead, hP, rtlPermOpt_some, htail,
        List.reverse_cons, Mealy.eval_append]
      simp [Mealy.run]

/-! ### The decomposition -/

/-- **The composite of the four primes is the right-to-left Mealy machine.** -/
theorem rtl_eq_comp :
    (homOf (outHom M hrev) ∘
        ((fun v => ((bcastMealy A Q).eval v.reverse).reverse) ∘
          ((labMealy M hrev).eval ∘ (fun w : List A => w.map some ++ [none])))) =
      fun w => (M.eval w.reverse).reverse := by
  funext w
  show homOf (outHom M hrev)
      (((bcastMealy A Q).eval ((labMealy M hrev).eval (w.map some ++ [none])).reverse).reverse)
    = _
  set L := labList M hrev 1 (w.map some) with hL
  set G := rtlProd M hrev w with hG
  have hinit : (labMealy M hrev).init = 1 := rfl
  have hlab : (labMealy M hrev).eval (w.map some ++ [none]) =
      L ++ [((none : Option A), G)] := by
    rw [Mealy.eval, hinit, labMealy_run, labList_append_sep, one_mul]
  have hLsome : ∀ y ∈ L.reverse, y.1.isSome :=
    fun y hy => labList_isSome M hrev w 1 y (List.mem_reverse.1 hy)
  have hbrun : (bcastMealy A Q).eval (((none : Option A), G) :: L.reverse) =
      ((none : Option A), G, (1 : Equiv.Perm Q)) ::
        L.reverse.map (fun y => (y.1, y.2, G)) := by
    have hstep : (bcastMealy A Q).step (bcastMealy A Q).init ((none : Option A), G) =
        (G, ((none : Option A), G, (1 : Equiv.Perm Q))) := rfl
    rw [Mealy.eval, Mealy.run_cons, hstep, bcastMealy_run_of_isSome L.reverse hLsome G]
  have hmain := homOf_outHom_labList M hrev w 1
  rw [one_mul, ← hL, ← hG] at hmain
  rw [hlab, List.reverse_append, List.reverse_singleton, List.singleton_append, hbrun,
    List.reverse_cons, ← List.map_reverse, List.reverse_reverse, hom_append, hmain]
  simp [homOf, outHom]

end RtlReversible

/-! ### The exercise -/

/-- Every function of the shortened list is one of the original primes. -/
lemma primeRationalFam_of_noRevRev {A B : Type} {f : List A → List B}
    (hf : PrimeRatNoRevRevFam A B f) : PrimeRationalFam A B f := by
  rcases hf with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

lemma compClosure_primeRational_of_noRevRev {A B : Type} {f : List A → List B}
    (hf : CompClosure PrimeRatNoRevRevFam A B f) : CompClosure PrimeRationalFam A B f := by
  induction hf with
  | base h => exact CompClosure.base (primeRationalFam_of_noRevRev h)
  | id A => exact CompClosure.id A
  | comp _ _ ih₁ ih₂ => exact CompClosure.comp ih₁ ih₂

/-- **A right-to-left reversible Mealy machine is a composition of the shortened list.**  This is
the content of Exercise `exer:no-reverse-reversible`. -/
theorem compClosure_noRevRev_rtlReversible {A B Q : Type} [Finite A] [Finite Q]
    (M : Mealy A B Q) (hrev : M.Reversible) :
    CompClosure PrimeRatNoRevRevFam A B (fun w => (M.eval w.reverse).reverse) := by
  rw [← rtl_eq_comp M hrev]
  have hsep : CompClosure PrimeRatNoRevRevFam A (Option A)
      (fun w : List A => w.map some ++ [none]) := by
    refine CompClosure.base (Or.inr (Or.inr (Or.inr ⟨Equiv.refl (Option A), ?_⟩)))
    funext w
    simp
  have hlab : CompClosure PrimeRatNoRevRevFam (Option A) (Option A × Equiv.Perm Q)
      (labMealy M hrev).eval :=
    CompClosure.base (Or.inl (Or.inl ⟨Equiv.Perm Q, inferInstance, labMealy M hrev, rfl,
      labMealy_reversible M hrev⟩))
  have hbcast : CompClosure PrimeRatNoRevRevFam (Option A × Equiv.Perm Q)
      (Option A × Equiv.Perm Q × Equiv.Perm Q)
      (fun v => ((bcastMealy A Q).eval v.reverse).reverse) :=
    CompClosure.base (Or.inr (Or.inl ⟨Equiv.Perm Q, inferInstance, bcastMealy A Q,
      by funext v; simp, bcastMealy_flipFlop A Q⟩))
  have hhom : CompClosure PrimeRatNoRevRevFam (Option A × Equiv.Perm Q × Equiv.Perm Q) B
      (homOf (outHom M hrev)) := CompClosure.base (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))
  exact CompClosure.comp (CompClosure.comp (CompClosure.comp hsep hlab) hbcast) hhom

/-- Every prime of Theorem `thm:rational-primes` is a composition of the shortened list. -/
theorem compClosure_noRevRev_of_prime {A B : Type} [Finite A] {f : List A → List B}
    (hf : PrimeRationalFam A B f) : CompClosure PrimeRatNoRevRevFam A B f := by
  rcases hf with h | h | h | h
  · exact CompClosure.base (Or.inl h)
  · rcases h with ⟨Q, hQ, M, hM, hr⟩ | h
    · have hfeq : f = fun w => (M.eval w.reverse).reverse := by
        funext w
        rw [hM]
        simp
      rw [hfeq]
      exact compClosure_noRevRev_rtlReversible M hr
    · exact CompClosure.base (Or.inr (Or.inl h))
  · exact CompClosure.base (Or.inr (Or.inr (Or.inl h)))
  · exact CompClosure.base (Or.inr (Or.inr (Or.inr h)))

lemma compClosure_noRevRev_of_compClosure :
    ∀ {A B : Type} {f : List A → List B}, CompClosure PrimeRationalFam A B f →
      Finite A → CompClosure PrimeRatNoRevRevFam A B f := by
  intro A B f h
  induction h with
  | base hf => intro hA; exact compClosure_noRevRev_of_prime hf
  | id A => intro _; exact CompClosure.id A
  | @comp A B C hB f g hf hg ihf ihg =>
      intro hA
      exact CompClosure.comp (ihf hA) (ihg hB)

/-- **Exercise `exer:no-reverse-reversible`.**  In the list of atomic functions of Theorem
`thm:rational-primes`, the reversal of a reversible Mealy machine is not needed: the compositions
of the shortened list `PrimeRatNoRevRevFam` -- prime Mealy machines, right-to-left *flip-flop*
Mealy machines, string homomorphisms and `w ↦ w#` -- are still exactly the rational functions. -/
theorem rational_primes_no_reverse_reversible {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    IsRationalFun f ↔ CompClosure PrimeRatNoRevRevFam A B f := by
  constructor
  · intro hf
    exact compClosure_noRevRev_of_compClosure
      ((rational_iff_prime_composition f).1 hf) inferInstance
  · intro hf
    exact PrimeRat.rationalFun_of_compClosure (compClosure_primeRational_of_noRevRev hf)
      inferInstance inferInstance

end Transducers.Exercises
