/-
Exercise `exer:forward-for-transducer` of the chapter *For-transducers*
(`polyregular-for.tex`) of *Transducers* (M. Bojańczyk).

The exercise asks to show that the functions computed by *forward* for-transducers -- those in
which every loop is of the first-to-last kind -- are exactly the composition closure of marked
squaring and the **rational** (not regular) functions.

The class on the right-hand side is `Transducers.Exercises.IsRatMarkedSquare` below: it is the
definition of the polyregular functions (Definition `def:polyregular-functions`) with "regular"
replaced by "rational".

The two inclusions are proved here outright.  Three of the four steps of the author's solution
ask for the proof of Theorem `thm:for-transducers-are-polyregular` to be replayed with the
direction of every loop tracked; they used to be assumed, and are now proved:

* `ForwardForClosedUnderComp` -- forward for-transducers are closed under composition.  This is
  Lemma `lem:for-closed-under-composition` with the extra bookkeeping that the composition
  construction of the project (`RequestProject/PartD/ForComp*.lean`) turns two forward programs
  into a forward one.  The construction itself keeps the direction of every loop it is given --
  the loop of `Transducers.lenProg` is first-to-last and `Transducers.tr` reproduces the
  directions of the nest it translates -- but it routes the inner program through the nest form
  `Transducers.for_nest_form`, which prepends one last-to-first loop; that nest form is replaced
  by the forward one, `Transducers.Exercises.for_nest_form_fwd`.  The proof is in
  `RequestProject/Exercises/ForwardComp.lean`.
* `ForwardPrenexNormalForm` -- Lemma `lemma:prenex-normal-form` for forward programs: a forward
  program is equivalent to one in prenex form all of whose loops are forward.  The project's
  construction (`RequestProject/PartD/ForPrenexTop.lean`) preserves the direction of every loop
  of the given program, and the *only* last-to-first loop it introduces is the one that binds a
  variable to the last position of the input.  That loop is removed by using the **first and the
  second** position of the input as the two designated positions rather than the first and the
  last; nothing in the merging construction uses that the second designated position is the last
  one, only that it comes after the first, so `Transducers.exec_merge` and
  `Transducers.trFor_spec` have been generalised, in place, to two designated positions in
  increasing order.  See `RequestProject/Exercises/ForwardPrenex.lean`.
* `ForwardStepRational` -- the one-step transducer of the enumeration, in the first-to-last
  direction, computes a rational function.  The project proves it is a streaming string
  transducer, hence regular (`Transducers.PolyEnum.isRegularFun_stepFun`); for `d = true` that
  transducer has three registers but is *order preserving* -- every update concatenates them in
  the fixed order `res`, `grp`, `cur` and only ever appends -- so it is a bimachine, hence
  rational.  See `RequestProject/Exercises/ForwardStep.lean`.

Everything else -- the two inclusions themselves, the enumeration of the tuples of a forward nest
of loops, and the base case of the enumeration -- is proved outright.  The right-to-left inclusion
also uses the two constructions of `RequestProject/Exercises/ForwardFor.lean`: marked squaring and
every rational function are computed by forward for-transducers.
-/
import RequestProject.Exercises.ForwardComp
import RequestProject.Exercises.ForwardStep
import RequestProject.Exercises.SeqSST
import RequestProject.PartD.PolyFor

namespace Transducers
namespace Exercises

open Transducers.PolyEnum

/-! ## Marked squaring and rational functions -/

/-- The family of prime functions of the exercise: rational functions and marked squaring.  This
is `Transducers.PolyregularFam` with "regular" replaced by "rational". -/
def RatMarkedFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  IsRationalFun f ∨
  (∃ (A₀ : Type) (e : A ≃ A₀) (e' : B ≃ A₀ ⊕ A₀),
      ∀ w, f w = (markedSquare A₀ (w.map e)).map e'.symm)

/-- **The composition closure of marked squaring and the rational functions**, the class on the
right-hand side of `exer:forward-for-transducer`. -/
def IsRatMarkedSquare {A B : Type} (f : List A → List B) : Prop :=
  CompClosure RatMarkedFam A B f

namespace IsRatMarkedSquare

variable {A B C : Type}

lemma congr {f g : List A → List B} (hf : IsRatMarkedSquare f) (h : ∀ w, f w = g w) :
    IsRatMarkedSquare g := (funext h : f = g) ▸ hf

lemma of_rational {f : List A → List B} (hf : IsRationalFun f) : IsRatMarkedSquare f :=
  CompClosure.base (Or.inl hf)

lemma comp {f : List A → List B} {g : List B → List C} [Finite B]
    (hf : IsRatMarkedSquare f) (hg : IsRatMarkedSquare g) : IsRatMarkedSquare (g ∘ f) :=
  CompClosure.comp hf hg

lemma comp' {f : List A → List B} {g : List B → List C} [Finite B] {h : List A → List C}
    (hf : IsRatMarkedSquare f) (hg : IsRatMarkedSquare g) (hh : ∀ w, h w = g (f w)) :
    IsRatMarkedSquare h :=
  (hf.comp hg).congr (fun w => (hh w).symm)

end IsRatMarkedSquare

lemma isRatMarkedSquare_id {A : Type} : IsRatMarkedSquare (id : List A → List A) :=
  CompClosure.id A

lemma isRatMarkedSquare_markedSquare (A : Type) : IsRatMarkedSquare (markedSquare A) :=
  CompClosure.base (Or.inr ⟨A, Equiv.refl _, Equiv.refl _, by intro w; simp⟩)

/-! ## The three steps of the solution -/

/-- **Forward for-transducers are closed under composition**: Lemma
`lem:for-closed-under-composition` with the directions of the loops tracked.  The finiteness
assumptions are not needed; they are kept so that the statement is the one that used to be
assumed. -/
theorem ForwardForClosedUnderComp :
    ∀ (A B C : Type) [Finite A] [Finite B] [Finite C] (f : List A → List B) (g : List B → List C),
      IsForwardFor f → IsForwardFor g → IsForwardFor (g ∘ f) := by
  intro _ _ _ _ _ _ _ _ hf hg
  exact isForwardFor_comp hf hg

/-- A program in prenex form all of whose loops are of the first-to-last kind. -/
def ForwardPrenexForm {A B : Type} (P : ForProg A B) : Prop :=
  ∃ (ls : List (Bool × ℕ)) (body epilogue : ForProg A B),
    (∀ p ∈ ls, p.1 = true) ∧ body.LoopFree ∧ epilogue.LoopFree ∧
      ForProg.OutputsAtMostOne body ∧ P = ForProg.seq (ForProg.nestLoops ls body) epilogue

/-- **Lemma `lemma:prenex-normal-form` for forward programs**: every forward for-program is
equivalent to a forward program in prenex form. -/
theorem ForwardPrenexNormalForm :
    ∀ (A B : Type) (P : ForProg A B), ForwardProg P →
      ∃ P' : ForProg A B, ForwardPrenexForm P' ∧ ∀ w, P'.eval w = P.eval w := by
  intro A B P hP
  obtain ⟨ls, body, epilogue, hfwd, hbody, hepi, hone, heval⟩ := forwardPrenex P hP
  exact ⟨ForProg.seq (ForProg.nestLoops ls body) epilogue,
    ⟨ls, body, epilogue, hfwd, hbody, hepi, hone, rfl⟩, heval⟩

/-- **The one-step transducer of the enumeration is rational in the first-to-last
direction.** -/
theorem ForwardStepRational :
    ∀ (A : Type) [Finite A] (k : ℕ), IsRationalFun (stepFun true A k) :=
  fun A _ k => isRationalFun_stepFun_true A k

/-! ## The scan of the enumeration is a rational function

The machine that scans the enumeration has a single register, and every one of its updates, as
well as its final output, appends a block to that register: it is append-only, so it computes a
sequential rewriting with a final output, which is a rational function. -/

section Scan

variable {A B : Type} (k m : ℕ) (body epilogue : ForProg A B) (vf : ℕ → Fin (k + 1))

/-- The block that the scanning machine appends when it reads one letter of the enumeration:
nothing inside a copy, the output of one iteration of the body at the end of a copy. -/
noncomputable def scanOut (q : ScanSt A k m) : Ann A k → List B
  | Ann.letter _ _ => []
  | Ann.sep => (bodyRun k m body vf q.bv q.cur).2
  | Ann.eos => []

/-- The block that the scanning machine appends at the end: the output of the epilogue. -/
noncomputable def scanFin (q : ScanSt A k m) : List B :=
  (ForProg.exec q.fst.toList epilogue (fun _ => 0) (extBV m q.bv)).2

lemma scanSST_step_append (q : ScanSt A k m) (z : Ann A k) :
    ((scanSST k m body epilogue vf).step q z).2 ()
      = Sum.inl () :: (scanOut k m body vf q z).map Sum.inr := by
  cases z <;> simp [scanSST, scanStep, scanOut]

lemma scanSST_final_append (q : ScanSt A k m) :
    (scanSST k m body epilogue vf).final q
      = Sum.inl () :: (scanFin k m epilogue q).map Sum.inr := rfl

/-- **The scan of the enumeration computes a rational function.**  This is the ingredient of the
solution of `exer:forward-for-transducer` that asks for the scan to be rational, and not merely
regular as in the proof of Theorem `thm:for-transducers-are-polyregular`. -/
theorem isRationalFun_scanFun [Finite A] [Finite B] :
    IsRationalFun (scanFun k m body epilogue vf) :=
  isRationalFun_of_appendOnlySST (scanSST k m body epilogue vf) (scanOut k m body vf)
    (scanFin k m epilogue) (scanSST_step_append k m body epilogue vf)
    (scanSST_final_append k m body epilogue vf)

end Scan

/-! ## From the class to forward for-transducers -/

/-- **The composition closure of marked squaring and the rational functions is computed by
forward for-transducers.** -/
theorem isForwardFor_of_isRatMarkedSquare :
    ∀ {A B : Type} {f : List A → List B}, IsRatMarkedSquare f →
      Finite A → Finite B → IsForwardFor f := by
  intro A B f hf
  induction hf with
  | @base A B f h =>
      intro hA hB
      haveI := hA
      haveI := hB
      rcases h with hrat | ⟨A₀, e, e', hfe⟩
      · exact isForwardFor_of_isRationalFun hrat
      · haveI : Finite A₀ := Finite.of_equiv A e
        refine IsForwardFor.congr
          (ForwardForClosedUnderComp A (A₀ ⊕ A₀) B _
            (fun v => v.map (e'.symm : A₀ ⊕ A₀ → B))
            (ForwardForClosedUnderComp A A₀ (A₀ ⊕ A₀) (fun w => w.map (e : A → A₀))
              (markedSquare A₀)
              (isForwardFor_of_isRationalFun (isRationalFun_map (e : A → A₀)))
              (isForwardFor_markedSquare A₀))
            (isForwardFor_of_isRationalFun (isRationalFun_map (e'.symm : A₀ ⊕ A₀ → B))))
          (fun w => (hfe w).symm)
  | id A =>
      intro hA _
      haveI := hA
      exact (isForwardFor_of_isRationalFun (isRationalFun_map (id : A → A))).congr
        (fun w => by simp)
  | comp _ _ ihf ihg =>
      intro hA hC
      exact ForwardForClosedUnderComp _ _ _ _ _ (ihf hA ‹Finite _›) (ihg ‹Finite _› hC)

/-! ## The enumeration of a forward nest of loops -/

section Enum

variable {A : Type}

/-- The output of a contextual rewriting that replaces every letter by its image and appends a
fixed string at the end. -/
lemma ctxAux_map_append {B : Type} (g : A → B) (c : List B) :
    ∀ (prev : Option A) (w : List A),
      ctxAux (fun _ next => match next with | some a => [g a] | none => c) prev w
        = w.map g ++ c := by
  intro prev w
  induction w generalizing prev with
  | nil => rfl
  | cons a w ih => simp [ih]

/-- Replacing every letter by its image and appending a fixed string is a rational function. -/
lemma isRationalFun_map_append_const {B : Type} [Finite A] [Finite B] (g : A → B) (c : List B) :
    IsRationalFun (fun w : List A => w.map g ++ c) := by
  have h := isRationalFun_ctxEval (Mo := Unit) (A := A) (B := B) (fun _ _ => ()) ()
    (fun _ _ next => match next with | some a => [g a] | none => c)
  have he : (fun w : List A => w.map g ++ c)
      = ctxEval (fun (_ : Unit) (_ : A) => ()) () (fun _ _ next =>
          match next with | some a => [g a] | none => c) := by
    funext w
    rw [ctxEval, ctxAux_map_append g c]
  exact he ▸ h

/-- The enumeration of the tuples of the empty nest of loops is a rational function: it is one
annotated copy of the input, followed by the separator and the end marker. -/
lemma isRationalFun_enum_nil [Finite A] :
    IsRationalFun (fun w : List A => enum 0 [] w) := by
  classical
  have h : IsRationalFun (fun w : List A =>
      w.map (fun a => Ann.letter a (fun j : Fin 0 => j.elim0))
        ++ ([Ann.sep, Ann.eos] : List (Ann A 0))) :=
    isRationalFun_map_append_const _ _
  have he : (fun w : List A => enum 0 [] w)
      = fun w : List A => w.map (fun a => Ann.letter a (fun j : Fin 0 => j.elim0))
          ++ ([Ann.sep, Ann.eos] : List (Ann A 0)) :=
    funext (fun w => enum_nil_eq (fun j : Fin 0 => j.elim0) w)
  exact he ▸ h

/-- **The enumeration of the tuples of positions visited by a forward nest of loops is a
composition of marked squaring and rational functions.** -/
theorem isRatMarkedSquare_enum [Finite A] :
    ∀ (L : List (Bool × ℕ)), (∀ p ∈ L, p.1 = true) → ∀ (k : ℕ), L.length = k →
      IsRatMarkedSquare (fun w : List A => enum k L w) := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
      intro _ k hk
      subst hk
      exact IsRatMarkedSquare.of_rational isRationalFun_enum_nil
  | append_singleton L a ih =>
      obtain ⟨d, x⟩ := a
      intro hL k hk
      have hd : d = true := hL (d, x) (by simp)
      subst hd
      have hL' : ∀ p ∈ L, p.1 = true := fun p hp => hL p (by simp [hp])
      have hk' : k = L.length + 1 := by simpa using hk.symm
      subst hk'
      haveI : Finite (Ann A L.length) := inferInstance
      refine IsRatMarkedSquare.comp' (g := stepFun true A L.length)
        ((ih hL' L.length rfl).comp' (isRatMarkedSquare_markedSquare (Ann A L.length))
          (fun w => rfl))
        (IsRatMarkedSquare.of_rational (ForwardStepRational A L.length)) (fun w => ?_)
      exact (stepFun_enum true x L w).symm

end Enum

/-! ## From forward for-transducers to the class -/

variable {A B : Type}

/-- **A forward for-transducer in prenex form computes a composition of marked squaring and
rational functions.** -/
theorem isRatMarkedSquare_of_forwardPrenex
    [Finite A] [Finite B] {P : ForProg A B} (hP : ForwardPrenexForm P) :
    IsRatMarkedSquare P.eval := by
  classical
  obtain ⟨L, body, epilogue, hfwd, hbody, hepi, hone, rfl⟩ := hP
  set k := L.length with hk
  set m := maxList body.boolVars + 1 with hm
  have hmlt : ∀ i ∈ body.boolVars, i < m := by
    intro i hi
    have := le_maxList body.boolVars i hi
    omega
  refine IsRatMarkedSquare.comp' (g := scanFun k m body epilogue
      (fun i => ⟨virt L i, Nat.lt_succ_of_le (virt_le L i)⟩))
    (isRatMarkedSquare_enum L hfwd k hk.symm)
    (IsRatMarkedSquare.of_rational (isRationalFun_scanFun k m body epilogue _))
    (fun w => ?_)
  exact (scan_enum k m body epilogue _ hk.symm hbody hepi (fun _ => rfl) hmlt w).symm

/-- **Every function computed by a forward for-transducer is a composition of marked squaring and
rational functions.** -/
theorem isRatMarkedSquare_of_isForwardFor [Finite A] [Finite B]
    {f : List A → List B} (hf : IsForwardFor f) : IsRatMarkedSquare f := by
  obtain ⟨P, hP, hval⟩ := hf
  obtain ⟨P', hpre', hval'⟩ := ForwardPrenexNormalForm A B P hP
  exact (isRatMarkedSquare_of_forwardPrenex hpre').congr
    (fun w => by rw [hval' w, hval w])

/-! ## The exercise -/

/-- **Exercise `exer:forward-for-transducer`.**  The functions computed by forward
for-transducers -- for-transducers all of whose loops are of the first-to-last kind -- are exactly
the composition closure of marked squaring and the rational functions.

The three steps of the author's solution that replay the proof of Theorem
`thm:for-transducers-are-polyregular` with the direction of every loop tracked are described in
the header of this file; all three are proved. -/
theorem forwardFor_iff_ratMarkedSquare [Finite A] [Finite B] (f : List A → List B) :
    IsForwardFor f ↔ IsRatMarkedSquare f :=
  ⟨fun hf => isRatMarkedSquare_of_isForwardFor hf,
    fun hf => isForwardFor_of_isRatMarkedSquare hf ‹Finite A› ‹Finite B›⟩

end Exercises
end Transducers
