/-
The exercises of the chapter on machine independent characterisations
(`myhill-nerode.tex`) of *Transducers* (M. Bojańczyk).
-/
import RequestProject.PartB.SeqChar
import RequestProject.PartB.SubseqDef
import RequestProject.PartB.Bimachine

/-!
# Minimal sequential transducers

Exercise `exer:minimal-sequential`: sequential transducers are ordered by the
number of states, and the minimal ones are unique up to isomorphism.

The solution of the book is the Myhill-Nerode argument.  For a function
`f : A* → B*` that is prefix preserving, the *residual* of an input string `u`
is the function

  `f_u : A* → B*`,  `f_u v = f(u)⁻¹ f(uv)`,

which here is `Transducers.Exercises.residOf f u v = (f (u ++ v)).drop (f u).length`.
The residuals form the state set of a canonical transducer
`Transducers.Exercises.canonSeq`, whose transitions are forced by `f` alone,
and every minimal transducer for `f` is isomorphic to it.
-/

namespace Transducers.Exercises

open Transducers

variable {A B : Type}

/-! ## Residuals -/

/-- The residual of `f` at the input string `u`: the function that maps `v` to the part of
`f (u ++ v)` that comes after `f u`.  For a prefix preserving `f` this is
`f(u)⁻¹ f(uv)` of the book. -/
def residOf (f : List A → List B) (u : List A) : List A → List B :=
  fun v => (f (u ++ v)).drop (f u).length

@[simp] lemma residOf_nil_arg (f : List A → List B) (u : List A) : residOf f u [] = [] := by
  simp [residOf]

lemma residOf_nil (f : List A → List B) (hnil : f [] = []) : residOf f [] = f := by
  funext v; simp [residOf, hnil]

/-- The residual of a prefix preserving function is again prefix preserving. -/
lemma residOf_prefix {f : List A → List B} (hpre : PrefixPreserving f) (u v w : List A) :
    residOf f u v <+: residOf f u (v ++ w) := by
  have h : f (u ++ v) <+: f (u ++ v ++ w) := hpre _ _ ⟨w, rfl⟩
  have := h.drop (f u).length
  simpa [residOf, List.append_assoc] using this

/-- Splitting a residual after its first letter. -/
lemma residOf_cons {f : List A → List B} (hpre : PrefixPreserving f) (u : List A) (a : A)
    (v : List A) :
    residOf f u (a :: v)
      = residOf f u [a] ++ (residOf f u (a :: v)).drop (residOf f u [a]).length := by
  have h : residOf f u [a] <+: residOf f u (a :: v) := by
    simpa using residOf_prefix hpre u [a] v
  obtain ⟨t, ht⟩ := h
  rw [← ht]
  simp

/-- The residuals are updated deterministically: the residual at `u ++ [a]` is obtained from
the residual at `u` alone. -/
lemma residOf_append_singleton {f : List A → List B} (hpre : PrefixPreserving f)
    (u : List A) (a : A) :
    residOf f (u ++ [a])
      = fun v => (residOf f u (a :: v)).drop (residOf f u [a]).length := by
  funext v
  have hle : (f u).length ≤ (f (u ++ [a])).length :=
    (hpre u (u ++ [a]) ⟨[a], rfl⟩).length_le
  have hcat : u ++ [a] ++ v = u ++ (a :: v) := by simp
  simp only [residOf, List.drop_drop, List.length_drop, hcat]
  congr 1
  omega

/-- The set of residuals of `f`. -/
def residuals (f : List A → List B) : Set (List A → List B) := Set.range (residOf f)

/-! ## Every transducer computes the residuals -/

/-- If a sequential transducer computes `f`, then the residual at `u` is the function computed
from the state reached after reading `u`. -/
lemma residOf_eq_run {Q : Type} (T : Sequential A B Q) (u : List A) :
    residOf T.eval u = T.run (strTrans T.transFun u T.init) := by
  funext v
  simp only [residOf, Sequential.eval]
  conv_lhs => rw [Sequential.run_append]
  simp

lemma residuals_subset_range_run {Q : Type} (T : Sequential A B Q) :
    residuals T.eval ⊆ Set.range T.run := by
  rintro _ ⟨u, rfl⟩
  exact ⟨_, (residOf_eq_run T u).symm⟩

lemma residuals_finite {Q : Type} [Finite Q] {f : List A → List B} {T : Sequential A B Q}
    (hT : T.eval = f) : (residuals f).Finite :=
  Set.Finite.subset (Set.finite_range _) (hT ▸ residuals_subset_range_run T)

/-! ## The canonical transducer -/

/-- The canonical sequential transducer of a prefix preserving function: its states are the
residuals of `f`, its initial state is `f` itself, and the transition reading `a` in the state
`f_u` outputs `f_u a` and moves to `f_{ua}`. -/
def canonSeq (f : List A → List B) (hpre : PrefixPreserving f) :
    Sequential A B (residuals f) where
  init := ⟨residOf f [], ⟨[], rfl⟩⟩
  step := fun x a =>
    (⟨fun v => (x.1 (a :: v)).drop (x.1 [a]).length, by
        obtain ⟨u, hu⟩ := x.2
        exact ⟨u ++ [a], by rw [residOf_append_singleton hpre, hu]⟩⟩,
      x.1 [a])

lemma canonSeq_run (f : List A → List B) (hpre : PrefixPreserving f) (u : List A)
    (h : residOf f u ∈ residuals f) (v : List A) :
    (canonSeq f hpre).run ⟨residOf f u, h⟩ v = residOf f u v := by
  induction v generalizing u h with
  | nil => simp
  | cons a v ih =>
      have hstep : ((canonSeq f hpre).step ⟨residOf f u, h⟩ a).1
          = ⟨residOf f (u ++ [a]), ⟨u ++ [a], rfl⟩⟩ := by
        apply Subtype.ext
        exact (residOf_append_singleton hpre u a).symm
      show ((canonSeq f hpre).step ⟨residOf f u, h⟩ a).2
          ++ (canonSeq f hpre).run ((canonSeq f hpre).step ⟨residOf f u, h⟩ a).1 v = _
      rw [hstep, ih (u ++ [a]) ⟨u ++ [a], rfl⟩]
      show residOf f u [a] ++ residOf f (u ++ [a]) v = _
      rw [residOf_append_singleton hpre]
      exact (residOf_cons hpre u a v).symm

lemma canonSeq_eval (f : List A → List B) (hpre : PrefixPreserving f) (hnil : f [] = []) :
    (canonSeq f hpre).eval = f := by
  funext v
  have := canonSeq_run f hpre [] ⟨[], rfl⟩ v
  simpa [Sequential.eval, canonSeq, residOf_nil f hnil] using this

/-! ## Minimality and isomorphism -/

/-- A state set `Q` is of minimal size among the sequential transducers computing `f`. -/
def MinimalFor (f : List A → List B) (Q : Type) : Prop :=
  ∀ (Q' : Type), Finite Q' → ∀ T' : Sequential A B Q', T'.eval = f → Nat.card Q ≤ Nat.card Q'

/-- Two sequential transducers are isomorphic if there is a bijection of their state sets that
matches the initial states and the transitions together with their outputs. -/
def SeqIso {Q₁ Q₂ : Type} (T₁ : Sequential A B Q₁) (T₂ : Sequential A B Q₂) : Prop :=
  ∃ e : Q₁ ≃ Q₂, e T₁.init = T₂.init ∧
    ∀ q a, T₂.step (e q) a = (e (T₁.step q a).1, (T₁.step q a).2)

lemma SeqIso.symm {Q₁ Q₂ : Type} {T₁ : Sequential A B Q₁} {T₂ : Sequential A B Q₂}
    (h : SeqIso T₁ T₂) : SeqIso T₂ T₁ := by
  obtain ⟨e, hinit, hstep⟩ := h
  refine ⟨e.symm, by rw [← hinit, Equiv.symm_apply_apply], fun q a => ?_⟩
  have := hstep (e.symm q) a
  rw [Equiv.apply_symm_apply] at this
  rw [this]
  simp

lemma SeqIso.trans {Q₁ Q₂ Q₃ : Type} {T₁ : Sequential A B Q₁} {T₂ : Sequential A B Q₂}
    {T₃ : Sequential A B Q₃} (h₁ : SeqIso T₁ T₂) (h₂ : SeqIso T₂ T₃) : SeqIso T₁ T₃ := by
  obtain ⟨e₁, hinit₁, hstep₁⟩ := h₁
  obtain ⟨e₂, hinit₂, hstep₂⟩ := h₂
  refine ⟨e₁.trans e₂, by simpa [hinit₁] using hinit₂, fun q a => ?_⟩
  simp only [Equiv.trans_apply]
  rw [hstep₂ (e₁ q) a, hstep₁ q a]

/-! ## A minimal transducer is the canonical one -/

/-- In a transducer with a minimal number of states, the map sending a state to the function it
computes is injective and its image is exactly the set of residuals. -/
lemma minimal_run_bijective {Q : Type} [Finite Q] {f : List A → List B}
    (T : Sequential A B Q) (hT : T.eval = f) (hmin : MinimalFor f Q) :
    Function.Injective T.run ∧ Set.range T.run = residuals f := by
  have hseq : IsSequential f := ⟨Q, ‹Finite Q›, T, hT⟩
  have hpre : PrefixPreserving f := hseq.prefixPreserving
  have hnil : f [] = [] := hseq.nil
  have hsub : residuals f ⊆ Set.range T.run := hT ▸ residuals_subset_range_run T
  have hfin : (residuals f).Finite := residuals_finite hT
  have hfinR : (Set.range T.run).Finite := Set.finite_range _
  -- minimality gives `card Q ≤ card (residuals f)`
  have h1 : Nat.card Q ≤ Nat.card (residuals f) := by
    have : Finite (residuals f) := hfin
    exact hmin _ this (canonSeq f hpre) (canonSeq_eval f hpre hnil)
  have h2 : Nat.card (residuals f) ≤ Nat.card (Set.range T.run) := by
    have : Finite (Set.range T.run) := hfinR
    exact Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  have h3 : Nat.card (Set.range T.run) ≤ Nat.card Q :=
    Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
  have heq1 : Nat.card (Set.range T.run) = Nat.card Q := le_antisymm h3 (h1.trans h2)
  have heq2 : Nat.card (residuals f) = Nat.card (Set.range T.run) :=
    le_antisymm h2 (h3.trans h1)
  constructor
  · have hb : Function.Bijective (Set.rangeFactorization T.run) :=
      (Nat.bijective_iff_surjective_and_card _).2
        ⟨Set.rangeFactorization_surjective, heq1.symm⟩
    intro x y hxy
    exact hb.1 (Subtype.ext hxy)
  · refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfinR).symm
    simpa [Set.ncard] using heq2.ge

/-- Every minimal sequential transducer for `f` is isomorphic to the canonical transducer whose
states are the residuals of `f`. -/
theorem seqIso_canonSeq {Q : Type} [Finite Q] {f : List A → List B}
    (T : Sequential A B Q) (hT : T.eval = f) (hmin : MinimalFor f Q)
    (hpre : PrefixPreserving f) :
    SeqIso T (canonSeq f hpre) := by
  obtain ⟨hinj, hrange⟩ := minimal_run_bijective T hT hmin
  have hmem : ∀ q : Q, T.run q ∈ residuals f := by
    intro q; rw [← hrange]; exact ⟨q, rfl⟩
  have hsurj : ∀ x : residuals f, ∃ q : Q, T.run q = x.1 := by
    intro x
    have hx : x.1 ∈ Set.range T.run := by rw [hrange]; exact x.2
    exact hx
  refine ⟨Equiv.ofBijective (fun q : Q => (⟨T.run q, hmem q⟩ : residuals f)) ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y hxy
    exact hinj (congrArg Subtype.val hxy)
  · intro x
    obtain ⟨q, hq⟩ := hsurj x
    exact ⟨q, Subtype.ext hq⟩
  · apply Subtype.ext
    have hf0 : f [] = [] := by rw [← hT]; rfl
    show T.run T.init = residOf f []
    rw [residOf_nil f hf0, ← hT]
    rfl
  · intro q a
    have hrun : ∀ (q : Q) (a : A) (v : List A),
        T.run q (a :: v) = (T.step q a).2 ++ T.run (T.step q a).1 v := fun _ _ _ => rfl
    have h2 : T.run q [a] = (T.step q a).2 := by rw [hrun]; simp
    apply Prod.ext
    · apply Subtype.ext
      show (fun v => (T.run q (a :: v)).drop (T.run q [a]).length) = T.run (T.step q a).1
      funext v
      rw [h2, hrun q a v]
      simp
    · exact h2

/-- **Exercise `exer:minimal-sequential`.**  Minimal sequential transducers are unique up to
isomorphism: any two sequential transducers computing the same function with the least possible
number of states are isomorphic.

Minimality is `MinimalFor`, and isomorphism is `SeqIso`: a bijection of the state sets that
matches the initial states and the transitions, outputs included. -/
theorem minimal_sequential_unique {Q₁ Q₂ : Type} [Finite Q₁] [Finite Q₂] {f : List A → List B}
    (T₁ : Sequential A B Q₁) (T₂ : Sequential A B Q₂)
    (h₁ : T₁.eval = f) (h₂ : T₂.eval = f)
    (m₁ : MinimalFor f Q₁) (m₂ : MinimalFor f Q₂) :
    SeqIso T₁ T₂ := by
  have hseq : IsSequential f := ⟨Q₁, ‹Finite Q₁›, T₁, h₁⟩
  have hpre : PrefixPreserving f := hseq.prefixPreserving
  exact (seqIso_canonSeq T₁ h₁ m₁ hpre).trans (seqIso_canonSeq T₂ h₂ m₂ hpre).symm

/-!
## Minimal subsequential transducers are not unique

Exercise `exer:minimal-subsequential`.  The counterexample of the book is the partial function
over a one-letter input alphabet with `ε ↦ ε` and `aⁿ ↦ c` for `n ≥ 1`.  One state does not
suffice, two states do, and there are two non-isomorphic ways of using two states: either the
first transition outputs `c`, or the end-of-input function of the second state does.
-/

/-- A state set `Q` is of minimal size among the subsequential transducers computing `f`. -/
def MinimalForSub (f : List A → Option (List B)) (Q : Type) : Prop :=
  ∀ (Q' : Type), Finite Q' → ∀ T' : Subsequential A B Q', T'.eval = f → Nat.card Q ≤ Nat.card Q'

/-- Isomorphism of subsequential transducers: a bijection of the state sets matching the initial
states, the transitions together with their outputs, and the end-of-input functions. -/
def SubseqIso {Q₁ Q₂ : Type} (T₁ : Subsequential A B Q₁) (T₂ : Subsequential A B Q₂) : Prop :=
  ∃ e : Q₁ ≃ Q₂, e T₁.toSequential.init = T₂.toSequential.init ∧
    (∀ q a, T₂.toSequential.step (e q) a
      = (e (T₁.toSequential.step q a).1, (T₁.toSequential.step q a).2)) ∧
    (∀ q, T₂.endOfInput (e q) = T₁.endOfInput q)

/-- The partial function of the counterexample: the empty input gives the empty output, and every
nonempty input gives the one-letter output `c`. -/
def lateOutput : List Unit → Option (List Unit) :=
  fun w => if w = [] then some [] else some [()]

/-- The first of the two minimal subsequential transducers: the transition out of the initial
state outputs `c`. -/
def lateOutputEarly : Subsequential Unit Unit Bool where
  init := false
  step := fun q _ => (true, if q then [] else [()])
  endOfInput := fun _ => some []

/-- The second of the two minimal subsequential transducers: all transitions are silent and the
end-of-input function of the second state outputs `c`. -/
def lateOutputLate : Subsequential Unit Unit Bool where
  init := false
  step := fun _ _ => (true, [])
  endOfInput := fun q => if q then some [()] else some []

private lemma lateOutputEarly_run_true (w : List Unit) :
    lateOutputEarly.toSequential.run true w = [] := by
  induction w with
  | nil => rfl
  | cons a w ih => show (_ : List Unit) ++ _ = _; simpa [lateOutputEarly] using ih

private lemma lateOutputLate_run (q : Bool) (w : List Unit) :
    lateOutputLate.toSequential.run q w = [] := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => show (_ : List Unit) ++ _ = _; simpa [lateOutputLate] using ih true

private lemma foldl_true_cons (δ : Bool → Unit → Bool) (hd : ∀ q a, δ q a = true)
    (a : Unit) (w : List Unit) (q : Bool) : List.foldl δ q (a :: w) = true := by
  rw [List.foldl_cons, hd]
  induction w with
  | nil => rfl
  | cons b w ih => rw [List.foldl_cons, hd]; exact ih

lemma lateOutputEarly_eval : lateOutputEarly.eval = lateOutput := by
  funext w
  cases w with
  | nil => rfl
  | cons a w =>
      have hst : strTrans lateOutputEarly.toSequential.transFun (a :: w)
          lateOutputEarly.toSequential.init = true :=
        foldl_true_cons _ (fun _ _ => rfl) a w _
      have hev : lateOutputEarly.toSequential.eval (a :: w) = [()] := by
        show ((if (false : Bool) then [] else [()]) : List Unit)
            ++ lateOutputEarly.toSequential.run true w = _
        rw [lateOutputEarly_run_true]
        simp
      show (lateOutputEarly.endOfInput _).map _ = _
      rw [hst, hev]
      show some (([()] : List Unit) ++ ([] : List Unit)) = _
      simp [lateOutput]

lemma lateOutputLate_eval : lateOutputLate.eval = lateOutput := by
  funext w
  cases w with
  | nil => rfl
  | cons a w =>
      have hst : strTrans lateOutputLate.toSequential.transFun (a :: w)
          lateOutputLate.toSequential.init = true :=
        foldl_true_cons _ (fun _ _ => rfl) a w _
      have hev : lateOutputLate.toSequential.eval (a :: w) = [] := lateOutputLate_run _ _
      show (lateOutputLate.endOfInput _).map _ = _
      rw [hst]
      show (some [()]).map _ = _
      rw [Option.map_some, hev]
      simp [lateOutput]

/-- One state is not enough for `lateOutput`. -/
lemma lateOutput_not_subsingleton {Q : Type} (T : Subsequential Unit Unit Q)
    (hT : T.eval = lateOutput) : ¬ Subsingleton Q := by
  intro hsub
  set q₀ := T.toSequential.init with hq₀
  set x := (T.toSequential.step q₀ ()).2 with hx
  have hstate : ∀ w : List Unit, strTrans T.toSequential.transFun w q₀ = q₀ := fun w =>
    Subsingleton.elim _ _
  have hrun : ∀ w : List Unit, T.toSequential.run q₀ w
      = (List.replicate w.length x).flatten := by
    intro w
    induction w with
    | nil => rfl
    | cons a w ih =>
        show (T.toSequential.step q₀ a).2 ++ T.toSequential.run (T.toSequential.step q₀ a).1 w = _
        rw [Subsingleton.elim (T.toSequential.step q₀ a).1 q₀, ih]
        cases a
        simp [hx, List.replicate_succ]
  have hev : ∀ w : List Unit, T.eval w
      = (T.endOfInput q₀).map (fun u => (List.replicate w.length x).flatten ++ u) := by
    intro w
    show (T.endOfInput (strTrans T.toSequential.transFun w T.toSequential.init)).map _ = _
    rw [← hq₀, hstate w]
    congr 1
    funext u
    show T.toSequential.run q₀ w ++ u = _
    rw [hrun]
  have h0 := hev []
  rw [hT] at h0
  simp only [lateOutput, List.length_nil, List.replicate_zero,
    List.flatten_nil, List.nil_append] at h0
  obtain ⟨y, hy, hy'⟩ := Option.map_eq_some_iff.1 h0.symm
  subst hy'
  have h1 := hev [()]
  rw [hT, hy] at h1
  simp only [lateOutput, List.length_cons, List.length_nil,
    List.append_nil, Option.map_some] at h1
  have hxval : x = [()] := by
    have := h1.symm
    simp only [if_neg (List.cons_ne_nil () []), Option.some.injEq] at this
    simpa using this
  have h2 := hev [(), ()]
  rw [hT, hy] at h2
  simp only [lateOutput, if_neg (List.cons_ne_nil () [()]), List.length_cons,
    List.length_nil, Option.map_some, Option.some.injEq] at h2
  rw [hxval] at h2
  simp at h2

/-- Two states are the minimum for `lateOutput`. -/
lemma lateOutput_minimal : MinimalForSub lateOutput Bool := by
  intro Q' hQ' T' hT'
  have : ¬ Subsingleton Q' := lateOutput_not_subsingleton T' hT'
  have h1 : ¬ (Nat.card Q' ≤ 1) := fun h => this (Finite.card_le_one_iff_subsingleton.1 h)
  simpa using h1

/-- **Exercise `exer:minimal-subsequential`.**  Minimal subsequential transducers are *not* unique
up to isomorphism: there is a partial function over a one-letter input alphabet, and two
subsequential transducers with the least possible number of states computing it, that are not
isomorphic.  The two transducers differ only in whether the letter `c` is produced by the first
transition or by the end-of-input function. -/
theorem minimal_subsequential_not_unique :
    ∃ (f : List Unit → Option (List Unit)) (T₁ T₂ : Subsequential Unit Unit Bool),
      T₁.eval = f ∧ T₂.eval = f ∧ MinimalForSub f Bool ∧ ¬ SubseqIso T₁ T₂ := by
  refine ⟨lateOutput, lateOutputEarly, lateOutputLate, lateOutputEarly_eval, lateOutputLate_eval,
    lateOutput_minimal, ?_⟩
  rintro ⟨e, hinit, hstep, -⟩
  have hfalse : e false = false := hinit
  have h := hstep false ()
  rw [hfalse] at h
  have : ((true : Bool), ([] : List Unit)) = (e true, [()]) := h
  exact absurd (congrArg Prod.snd this) (by simp)

/-!
## Minimal bimachines are not unique

Exercise `exer:non-minimal-bimachine`.  Bimachines are ordered by the number of states of the
suffix automaton.  The counterexample of the book is already a language: the strings of even
length over a one-letter alphabet, seen as the function that outputs a single bit.  One bimachine
computes the parity in the prefix automaton and produces the output in the last gap; the other
computes the parity in the suffix automaton and produces the output in the first gap.  Both have
two states in the suffix automaton, which is the least possible, and they are not isomorphic.
-/

/-- The function of the counterexample: one output bit saying whether the input has even
length. -/
def evenParity : List Unit → List Bool := fun w => [decide (w.length % 2 = 0)]

/-- A state set `S` is of minimal size among the suffix automata of the bimachines computing
`f`. -/
def MinimalSuffix (f : List A → List B) (S : Type) : Prop :=
  ∀ (P' S' : Type), Finite P' → Finite S' → ∀ M : Bimachine A B P' S', M.eval = f →
    Nat.card S ≤ Nat.card S'

/-- Isomorphism of bimachines: bijections of the two state sets matching the initial states, the
transitions and the output function. -/
def BimIso {P₁ S₁ P₂ S₂ : Type} (M₁ : Bimachine A B P₁ S₁) (M₂ : Bimachine A B P₂ S₂) : Prop :=
  ∃ (eP : P₁ ≃ P₂) (eS : S₁ ≃ S₂),
    eP M₁.prefixInit = M₂.prefixInit ∧
    (∀ p a, M₂.prefixStep (eP p) a = eP (M₁.prefixStep p a)) ∧
    eS M₁.suffixInit = M₂.suffixInit ∧
    (∀ s a, M₂.suffixStep (eS s) a = eS (M₁.suffixStep s a)) ∧
    (∀ p s, M₂.out (eP p) (eS s) = M₁.out p s)

private lemma strTrans_not (l : List Unit) (q : Bool) :
    strTrans (fun (s : Bool) (_ : Unit) => !s) l q = if l.length % 2 = 0 then q else !q := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih =>
      show strTrans (fun (s : Bool) (_ : Unit) => !s) l (!q) = _
      rw [ih]
      rcases Nat.even_or_odd l.length with h | h
      · have h0 : l.length % 2 = 0 := Nat.even_iff.1 h
        simp [h0, Nat.add_mod]
      · have h1 : l.length % 2 = 1 := Nat.odd_iff.1 h
        simp [h1, Nat.add_mod]

private lemma strTrans_const_false (l : List Unit) (q : Bool) :
    strTrans (fun (_ : Bool) (_ : Unit) => false) l q = if l = [] then q else false := by
  cases l with
  | nil => rfl
  | cons a l =>
      show strTrans (fun (_ : Bool) (_ : Unit) => false) l false = _
      rw [if_neg (List.cons_ne_nil a l)]
      clear a
      induction l with
      | nil => rfl
      | cons b l ih => exact ih

/-- The first bimachine: the prefix automaton computes the parity, the suffix automaton tests
whether the suffix is empty, and the output is produced in the last gap. -/
def bimEvenPrefix : Bimachine Unit Bool Bool Bool where
  prefixInit := true
  prefixStep := fun p _ => !p
  suffixInit := true
  suffixStep := fun _ _ => false
  out := fun p s => if s then [p] else []

/-- The second bimachine: the prefix automaton tests whether the prefix is empty, the suffix
automaton computes the parity, and the output is produced in the first gap. -/
def bimEvenSuffix : Bimachine Unit Bool Bool Bool where
  prefixInit := true
  prefixStep := fun _ _ => false
  suffixInit := true
  suffixStep := fun s _ => !s
  out := fun p s => if p then [s] else []

private lemma bimEvenPrefix_evalFrom (p : Bool) (w : List Unit) :
    bimEvenPrefix.evalFrom p w = [if w.length % 2 = 0 then p else !p] := by
  induction w generalizing p with
  | nil => simp [bimEvenPrefix]
  | cons a w ih =>
      rw [Bimachine.evalFrom_cons]
      have hs : strTrans bimEvenPrefix.suffixStep (a :: w).reverse bimEvenPrefix.suffixInit
          = false := by
        rw [show bimEvenPrefix.suffixStep = fun (_ : Bool) (_ : Unit) => false from rfl,
          strTrans_const_false]
        simp
      rw [hs]
      show ([] : List Bool) ++ bimEvenPrefix.evalFrom (!p) w = _
      rw [List.nil_append, ih]
      rcases Nat.even_or_odd w.length with h | h
      · have h0 : w.length % 2 = 0 := Nat.even_iff.1 h
        simp [h0, Nat.add_mod]
      · have h1 : w.length % 2 = 1 := Nat.odd_iff.1 h
        simp [h1, Nat.add_mod]

lemma bimEvenPrefix_eval : bimEvenPrefix.eval = evenParity := by
  funext w
  rw [Bimachine.eval_eq_evalFrom, bimEvenPrefix_evalFrom]
  show [if w.length % 2 = 0 then true else !true] = _
  by_cases h : w.length % 2 = 0 <;> simp [evenParity, h]

private lemma bimEvenSuffix_evalFrom_false (w : List Unit) :
    bimEvenSuffix.evalFrom false w = [] := by
  induction w with
  | nil => simp [bimEvenSuffix]
  | cons a w ih =>
      rw [Bimachine.evalFrom_cons]
      show ([] : List Bool) ++ bimEvenSuffix.evalFrom false w = _
      rw [List.nil_append, ih]

lemma bimEvenSuffix_eval : bimEvenSuffix.eval = evenParity := by
  funext w
  rw [Bimachine.eval_eq_evalFrom]
  cases w with
  | nil => simp [bimEvenSuffix, evenParity]
  | cons a w =>
      rw [Bimachine.evalFrom_cons]
      have hs : strTrans bimEvenSuffix.suffixStep (a :: w).reverse bimEvenSuffix.suffixInit
          = if (a :: w).length % 2 = 0 then true else false := by
        rw [show bimEvenSuffix.suffixStep = fun (s : Bool) (_ : Unit) => !s from rfl,
          strTrans_not]
        simp [bimEvenSuffix]
      show bimEvenSuffix.out bimEvenSuffix.prefixInit _ ++ bimEvenSuffix.evalFrom false w = _
      rw [hs, bimEvenSuffix_evalFrom_false]
      show (if (true : Bool) then [if (a :: w).length % 2 = 0 then true else false] else [])
        ++ ([] : List Bool) = _
      simp [evenParity]

/-- A suffix automaton with one state is not enough for `evenParity`. -/
lemma evenParity_suffix_not_subsingleton {P' S' : Type} (M : Bimachine Unit Bool P' S')
    (hM : M.eval = evenParity) : ¬ Subsingleton S' := by
  intro hsub
  have h0 : M.out M.prefixInit M.suffixInit = [true] := by
    have := congrFun hM []
    rw [Bimachine.eval_eq_evalFrom, Bimachine.evalFrom_nil] at this
    simpa [evenParity] using this
  have h1 := congrFun hM [()]
  rw [Bimachine.eval_eq_evalFrom, Bimachine.evalFrom_cons,
    Subsingleton.elim (strTrans M.suffixStep ([()] : List Unit).reverse M.suffixInit)
      M.suffixInit, h0] at h1
  simp only [evenParity, List.length_cons, List.length_nil] at h1
  have := congrArg (List.take 1) h1
  simp at this

/-- Two states in the suffix automaton are the minimum for `evenParity`. -/
lemma evenParity_minimalSuffix : MinimalSuffix evenParity Bool := by
  intro P' S' _ hS' M hM
  have h : ¬ Subsingleton S' := evenParity_suffix_not_subsingleton M hM
  have h1 : ¬ (Nat.card S' ≤ 1) := fun hc => h (Finite.card_le_one_iff_subsingleton.1 hc)
  simpa using h1

/-- **Exercise `exer:non-minimal-bimachine`.**  Bimachines with a minimal number of states in the
suffix automaton are *not* unique up to isomorphism: for the function that says whether the input
has even length, over a one-letter alphabet, there are two bimachines with two states in the
suffix automaton — the least possible — that are not isomorphic. -/
theorem minimal_bimachine_not_unique :
    ∃ (f : List Unit → List Bool) (M₁ M₂ : Bimachine Unit Bool Bool Bool),
      M₁.eval = f ∧ M₂.eval = f ∧ MinimalSuffix f Bool ∧ ¬ BimIso M₁ M₂ := by
  refine ⟨evenParity, bimEvenPrefix, bimEvenSuffix, bimEvenPrefix_eval, bimEvenSuffix_eval,
    evenParity_minimalSuffix, ?_⟩
  rintro ⟨eP, eS, hinit, hstep, -, -, -⟩
  have hT : eP true = true := hinit
  have e1 : eP false = false := by
    have := hstep true ()
    rw [hT] at this
    exact this.symm
  have e2 : (false : Bool) = true := by
    have h := hstep false ()
    rw [e1] at h
    rw [show bimEvenSuffix.prefixStep false () = false from rfl,
      show bimEvenPrefix.prefixStep false () = true from rfl, hT] at h
    exact h
  exact absurd e2 (by simp)

end Transducers.Exercises
