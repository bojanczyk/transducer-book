/-
Auxiliary facts used by the solutions to the exercises of Parts B and C of
*Transducers* (M. Bojańczyk), which are formalised in
`RequestProject/Exercises/PartBC.lean`.

The book takes these for granted inside the solutions:

* rational relations are symmetric in the input and the output (swapping the two
  labels of every transition of an nfa with output), so the inverse of a
  rational relation is rational;
* a few small regular languages, given by explicit deterministic automata, that
  the guess-and-check construction `Transducers.isRationalRel_of_regular_nivat`
  is applied to;
* the non-regularity of the languages that the counterexamples of the exercises
  produce, proved with the pumping lemma.
-/
import RequestProject.Exercises.IntroAux
import RequestProject.PartB.RationalStatements
import RequestProject.PartB.GuessCheck
import RequestProject.PartB.UniformFun
import RequestProject.PartB.RatIndex
import RequestProject.PartC.MSO
import RequestProject.PartC.MarkLogic
import RequestProject.PartC.MapLiftPrime
import RequestProject.PartC.MapLiftRat
import RequestProject.PartC.RatSeq

namespace Transducers
namespace Exercises

open LabAut NFAO

/-! ## Regularity of some explicit languages -/

/-- A language accepted by a deterministic automaton with finitely many states is regular. -/
lemma isRegular_of_dfa {A σ : Type} [Finite σ] (D : DFA A σ) {L : Language A}
    (h : D.accepts = L) : L.IsRegular := by
  letI : Fintype σ := Fintype.ofFinite σ
  exact ⟨σ, inferInstance, D, h⟩

/-- The language of all strings is regular. -/
lemma isRegular_univ {A : Type} : Language.IsRegular (Set.univ : Language A) :=
  isRegular_of_dfa (σ := Unit) ⟨fun _ _ => (), (), Set.univ⟩
    (by ext w; simp [DFA.accepts, DFA.acceptsFrom])

/-- The language of the strings all of whose letters satisfy a decidable
predicate is regular. -/
lemma isRegular_forall_mem {A : Type} (P : A → Prop) [DecidablePred P] :
    Language.IsRegular ({u : List A | ∀ a ∈ u, P a} : Language A) := by
  refine isRegular_of_dfa (σ := Bool)
    ⟨fun s a => s && decide (P a), true, {true}⟩ ?_
  have key : ∀ (u : List A) (s : Bool),
      u.foldl (fun s a => s && decide (P a)) s = (s && decide (∀ a ∈ u, P a)) := by
    intro u
    induction u with
    | nil => intro s; simp
    | cons a u ih =>
        intro s
        rw [List.foldl_cons, ih]
        by_cases h : P a <;> simp [h]
  ext u
  simp only [DFA.mem_accepts, DFA.eval, DFA.evalFrom, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [key u true]
  simp only [Bool.true_and, decide_eq_true_eq]
  exact Iff.rfl

/-- The deterministic automaton for the language `false* true*`: the state
records whether a `true` has already been read, and `none` is the sink reached
when a `false` follows a `true`. -/
def sortedDFA : DFA Bool (Option Bool) where
  step := fun s a => match s, a with
    | some false, false => some false
    | some false, true => some true
    | some true, false => none
    | some true, true => some true
    | none, _ => none
  start := some false
  accept := {some false, some true}

private lemma sortedDFA_dead (u : List Bool) : sortedDFA.evalFrom none u ∉ sortedDFA.accept := by
  induction u with
  | nil => simp [sortedDFA]
  | cons a u ih => simpa [DFA.evalFrom, sortedDFA] using ih

private lemma sortedDFA_true (u : List Bool) :
    sortedDFA.evalFrom (some true) u ∈ sortedDFA.accept ↔ ∃ m, u = List.replicate m true := by
  induction u with
  | nil => exact ⟨fun _ => ⟨0, rfl⟩, fun _ => by simp [sortedDFA, DFA.evalFrom]⟩
  | cons a u ih =>
      cases a with
      | false =>
          constructor
          · intro h
            exact absurd h (by
              have : sortedDFA.evalFrom (some true) (false :: u) = sortedDFA.evalFrom none u := rfl
              rw [this]; exact sortedDFA_dead u)
          · rintro ⟨m, hm⟩
            cases m with
            | zero => simp at hm
            | succ m => rw [List.replicate_succ] at hm; simp at hm
      | true =>
          have h1 : sortedDFA.evalFrom (some true) (true :: u)
              = sortedDFA.evalFrom (some true) u := rfl
          rw [h1, ih]
          constructor
          · rintro ⟨m, rfl⟩; exact ⟨m + 1, by rw [List.replicate_succ]⟩
          · rintro ⟨m, hm⟩
            cases m with
            | zero => simp at hm
            | succ m => rw [List.replicate_succ] at hm; exact ⟨m, (List.cons_inj_right _).1 hm⟩

private lemma sortedDFA_false (u : List Bool) :
    sortedDFA.evalFrom (some false) u ∈ sortedDFA.accept ↔
      ∃ n m, u = List.replicate n false ++ List.replicate m true := by
  induction u with
  | nil => exact ⟨fun _ => ⟨0, 0, rfl⟩, fun _ => by simp [sortedDFA, DFA.evalFrom]⟩
  | cons a u ih =>
      cases a with
      | false =>
          have h1 : sortedDFA.evalFrom (some false) (false :: u)
              = sortedDFA.evalFrom (some false) u := rfl
          rw [h1, ih]
          constructor
          · rintro ⟨n, m, rfl⟩
            exact ⟨n + 1, m, by rw [List.replicate_succ, List.cons_append]⟩
          · rintro ⟨n, m, hm⟩
            cases n with
            | zero =>
                simp only [List.replicate_zero, List.nil_append] at hm
                cases m with
                | zero => simp at hm
                | succ m => rw [List.replicate_succ] at hm; simp at hm
            | succ n =>
                rw [List.replicate_succ, List.cons_append] at hm
                exact ⟨n, m, (List.cons_inj_right _).1 hm⟩
      | true =>
          have h1 : sortedDFA.evalFrom (some false) (true :: u)
              = sortedDFA.evalFrom (some true) u := rfl
          rw [h1, sortedDFA_true]
          constructor
          · rintro ⟨m, rfl⟩
            exact ⟨0, m + 1, by simp [List.replicate_succ]⟩
          · rintro ⟨n, m, hm⟩
            cases n with
            | zero =>
                simp only [List.replicate_zero, List.nil_append] at hm
                cases m with
                | zero => simp at hm
                | succ m =>
                    rw [List.replicate_succ] at hm
                    exact ⟨m, (List.cons_inj_right _).1 hm⟩
            | succ n => rw [List.replicate_succ, List.cons_append] at hm; simp at hm

/-- The language `false* true*` is regular. -/
lemma isRegular_sortedBool :
    Language.IsRegular ({u : List Bool | ∃ n m, u = List.replicate n false ++ List.replicate m true}
      : Language Bool) := by
  refine isRegular_of_dfa sortedDFA ?_
  ext u
  exact sortedDFA_false u

/-! ## The inverse of a rational relation

Rational relations are symmetric with respect to input and output: swapping the
input and the output label on every transition of an nfa with output gives an
automaton for the inverse relation. -/

/-- Swapping the input and the output label of a transition. -/
def swapT {A B Q : Type} (t : Q × List A × List B × Q) : Q × List B × List A × Q :=
  (t.1, t.2.2.1, t.2.1, t.2.2.2)

/-- The nfa with output for the inverse relation: the input and the output label
of every transition are swapped. -/
def swapAut {A B Q : Type} (M : NFAO A B Q) : NFAO B A Q where
  init := M.init
  final := M.final
  δ := swapT '' M.δ
  δ_finite := M.δ_finite.image _

@[simp] lemma swapT_swapT {A B Q : Type} (t : Q × List A × List B × Q) :
    swapT (swapT t) = t := rfl

@[simp] lemma swapAut_swapAut {A B Q : Type} (M : NFAO A B Q) : swapAut (swapAut M) = M := by
  cases M with
  | mk init final δ hδ =>
    simp only [swapAut, LabAut.mk.injEq, true_and]
    rw [Set.image_image]
    simp

lemma inputOf_map_swapT {A B Q : Type} (ts : List (Q × List A × List B × Q)) :
    LabAut.inputOf (ts.map swapT) = NFAO.outputOf ts := by
  simp [LabAut.inputOf, NFAO.outputOf, LabAut.labelsOf, List.map_map, Function.comp_def, swapT]

lemma outputOf_map_swapT {A B Q : Type} (ts : List (Q × List A × List B × Q)) :
    NFAO.outputOf (ts.map swapT) = LabAut.inputOf ts := by
  simp [LabAut.inputOf, NFAO.outputOf, LabAut.labelsOf, List.map_map, Function.comp_def, swapT]

lemma path_swapAut {A B Q : Type} {M : NFAO A B Q} {q p : Q}
    {ts : List (Q × List A × List B × Q)} (h : M.Path q ts p) :
    (swapAut M).Path q (ts.map swapT) p := by
  induction h with
  | nil q => exact LabAut.Path.nil q
  | cons ht _ ih => exact LabAut.Path.cons ⟨_, ht, rfl⟩ ih

lemma rel_swapAut {A B Q : Type} (M : NFAO A B Q) (w : List A) (v : List B) :
    (swapAut M).rel v w ↔ M.rel w v := by
  constructor
  · rintro ⟨ts, ⟨q, hq, p, hp, hpath⟩, hin, hout⟩
    refine ⟨ts.map swapT, ⟨q, hq, p, hp, ?_⟩, ?_, ?_⟩
    · have := path_swapAut hpath
      rwa [swapAut_swapAut] at this
    · rw [inputOf_map_swapT, hout]
    · rw [outputOf_map_swapT, hin]
  · rintro ⟨ts, ⟨q, hq, p, hp, hpath⟩, hin, hout⟩
    exact ⟨ts.map swapT, ⟨q, hq, p, hp, path_swapAut hpath⟩,
      by rw [inputOf_map_swapT, hout], by rw [outputOf_map_swapT, hin]⟩

/-- **The inverse of a rational relation is rational.**  This is the symmetry of
rational relations with respect to input and output, which the book uses in
several of the solutions. -/
theorem isRationalRel_inv {A B : Type} {R : List A → List B → Prop} (hR : IsRationalRel R) :
    IsRationalRel (fun (v : List B) (w : List A) => R w v) := by
  obtain ⟨Q, hQ, M, hM⟩ := hR
  exact ⟨Q, hQ, swapAut M, fun v w => (hM w v).trans (rel_swapAut M w v).symm⟩

/-- A relation that agrees with a rational relation is rational. -/
lemma isRationalRel_congr {A B : Type} {R R' : List A → List B → Prop}
    (h : IsRationalRel R) (hRR : ∀ w v, R' w v ↔ R w v) : IsRationalRel R' :=
  let ⟨Q, hQ, M, hM⟩ := h
  ⟨Q, hQ, M, fun w v => (hRR w v).trans (hM w v)⟩

/-- Every list of units is a power of the unit. -/
lemma list_unit_eq_replicate (l : List Unit) : l = List.replicate l.length () := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a; rw [List.length_cons, List.replicate_succ, ← ih]

/-- Two lists of units are equal as soon as they have the same length. -/
lemma list_unit_eq_iff (l l' : List Unit) : l = l' ↔ l.length = l'.length := by
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  rw [list_unit_eq_replicate l, list_unit_eq_replicate l', h]

/-! ## Paths, their inputs and their outputs

The bounds of Exercise `exer:rational-output-size` are read off a single path. -/

/-- Only finitely many strings have bounded length. -/
lemma finite_lists_length_le {B : Type} [Finite B] (n : ℕ) :
    {v : List B | v.length ≤ n}.Finite := by
  induction n with
  | zero =>
      refine (Set.finite_singleton []).subset ?_
      intro v hv
      exact List.length_eq_zero_iff.mp (Nat.le_zero.mp hv)
  | succ n ih =>
      refine ((Set.finite_singleton []).union
        (((Set.finite_univ (α := B)).prod ih).image (fun p => p.1 :: p.2))).subset ?_
      intro v hv
      cases v with
      | nil => exact Or.inl rfl
      | cons b v =>
          refine Or.inr ⟨(b, v), ⟨trivial, ?_⟩, rfl⟩
          simp only [Set.mem_setOf_eq, List.length_cons] at hv ⊢
          omega

/-- Every transition of a path is a transition of the automaton. -/
lemma path_mem_delta {A B Q : Type} {M : NFAO A B Q} {q p : Q}
    {ts : List (Q × List A × List B × Q)} (h : M.Path q ts p) : ∀ t ∈ ts, t ∈ M.δ := by
  induction h with
  | nil q => intro t ht; simp at ht
  | @cons q u l q' ts p ht _ ih =>
      intro t htt
      rcases List.mem_cons.1 htt with rfl | htt
      · exact ht
      · exact ih t htt

/-- The output of a path is at most `K` times its length, if every transition
outputs at most `K` letters. -/
lemma outputOf_length_le {A B Q : Type} {M : NFAO A B Q} {K : ℕ}
    (hK : ∀ t ∈ M.δ, (t.2.2.1 : List B).length ≤ K) :
    ∀ ts : List (Q × List A × List B × Q), (∀ t ∈ ts, t ∈ M.δ) →
      (NFAO.outputOf ts).length ≤ K * ts.length := by
  intro ts
  induction ts with
  | nil => intro _; simp
  | cons t ts ih =>
      intro hmem
      rw [NFAO.outputOf_cons, List.length_append, List.length_cons]
      have h1 := hK t (hmem t (by simp))
      have h2 := ih (fun t' ht' => hmem t' (by simp [ht']))
      calc t.2.2.1.length + (NFAO.outputOf ts).length ≤ K + K * ts.length := by omega
        _ = K * (ts.length + 1) := by ring

/-- The input of a path whose transitions all read a single letter has the
length of the path. -/
lemma inputOf_length_of_one {A B Q : Type} :
    ∀ ts : List (Q × List A × List B × Q), (∀ t ∈ ts, (t.2.1 : List A).length = 1) →
      (LabAut.inputOf ts).length = ts.length := by
  intro ts
  induction ts with
  | nil => intro _; simp
  | cons t ts ih =>
      intro hmem
      rw [LabAut.inputOf_cons, List.length_append, List.length_cons,
        hmem t (by simp), ih (fun t' ht' => hmem t' (by simp [ht']))]
      omega

/-! ## Non-regularity by the Myhill-Nerode theorem

The counterexamples of the exercises produce languages that are not regular.
The book proves this with the pumping lemma; here it is more convenient to use
Mathlib's form of the Myhill-Nerode theorem, that a regular language has
finitely many left quotients. -/

/-- A language with infinitely many left quotients is not regular. -/
lemma not_isRegular_of_leftQuotient_injective {A : Type} {L : Language A} (x : ℕ → List A)
    (hinj : Function.Injective (fun n => L.leftQuotient (x n))) : ¬ L.IsRegular := fun h =>
  absurd h.finite_range_leftQuotient
    (Set.infinite_of_injective_forall_mem hinj (fun n => Set.mem_range_self (x n)))

/-- The number of `false`s in `falseⁿ trueᵐ`. -/
@[simp] lemma count_false_replicate (n m : ℕ) :
    (List.replicate n false ++ List.replicate m true).count false = n := by
  simp [List.count_append, List.count_replicate]

/-- The number of `true`s in `falseⁿ trueᵐ`. -/
@[simp] lemma count_true_replicate (n m : ℕ) :
    (List.replicate n false ++ List.replicate m true).count true = m := by
  simp [List.count_append, List.count_replicate]

/-- The language `{ falseⁿ trueⁿ }` is not regular. -/
lemma not_isRegular_eqReplicate :
    ¬ Language.IsRegular ({v : List Bool | ∃ n, v = List.replicate n false ++ List.replicate n true}
      : Language Bool) := by
  refine not_isRegular_of_leftQuotient_injective (fun n => List.replicate n false) ?_
  intro m n hmn
  have hmn' : Language.leftQuotient
      {v : List Bool | ∃ k, v = List.replicate k false ++ List.replicate k true}
      (List.replicate m false)
      = Language.leftQuotient
        {v : List Bool | ∃ k, v = List.replicate k false ++ List.replicate k true}
        (List.replicate n false) := hmn
  have hm : List.replicate m true ∈
      Language.leftQuotient {v : List Bool |
        ∃ k, v = List.replicate k false ++ List.replicate k true} (List.replicate m false) :=
    ⟨m, rfl⟩
  rw [hmn'] at hm
  obtain ⟨k, hk⟩ := hm
  have h1 := congrArg (fun l : List Bool => l.count false) hk
  have h2 := congrArg (fun l : List Bool => l.count true) hk
  simp only [count_false_replicate, count_true_replicate] at h1 h2
  omega

/-- The language of the strings over `{false, true}` with as many `false`s as
`true`s is not regular. -/
lemma not_isRegular_balanced :
    ¬ Language.IsRegular ({w : List Bool | w.count false = w.count true} : Language Bool) := by
  refine not_isRegular_of_leftQuotient_injective (fun n => List.replicate n false) ?_
  intro m n hmn
  have hmn' : Language.leftQuotient {w : List Bool | w.count false = w.count true}
      (List.replicate m false)
      = Language.leftQuotient {w : List Bool | w.count false = w.count true}
        (List.replicate n false) := hmn
  have hm : List.replicate m true ∈
      Language.leftQuotient {w : List Bool | w.count false = w.count true}
        (List.replicate m false) :=
    (count_false_replicate m m).trans (count_true_replicate m m).symm
  rw [hmn'] at hm
  have : (List.replicate n false ++ List.replicate m true).count false
      = (List.replicate n false ++ List.replicate m true).count true := hm
  simp only [count_false_replicate, count_true_replicate] at this
  omega

/-- The language `{ falseⁱ trueʲ | j ≤ i }` used in the first item of Exercise
`exer:non-rational`. -/
def atMostAsMany : Language Bool :=
  {w | ∃ i j : ℕ, j ≤ i ∧ w = List.replicate i false ++ List.replicate j true}

/-- The blocks `falseⁿ trueᵐ` determine `n` and `m`. -/
lemma replicate_append_inj {i j p q : ℕ}
    (h : List.replicate i false ++ List.replicate j true
      = List.replicate p false ++ List.replicate q true) : i = p ∧ j = q :=
  ⟨by simpa [List.count_append, List.count_replicate] using congrArg (List.count false) h,
    by simpa [List.count_append, List.count_replicate] using congrArg (List.count true) h⟩

/-- The language `{ falseⁱ trueʲ | j ≤ i }` is not regular. -/
lemma not_isRegular_atMostAsMany : ¬ atMostAsMany.IsRegular := by
  refine not_isRegular_of_leftQuotient_injective (fun n => List.replicate n false) ?_
  have key : ∀ i j : ℕ,
      (List.replicate i false ++ List.replicate j true) ∈ atMostAsMany ↔ j ≤ i := by
    intro i j
    constructor
    · rintro ⟨p, q, hpq, h⟩
      obtain ⟨rfl, rfl⟩ := replicate_append_inj h
      exact hpq
    · intro h; exact ⟨i, j, h, rfl⟩
  intro m n hmn
  have hmn' : atMostAsMany.leftQuotient (List.replicate m false)
      = atMostAsMany.leftQuotient (List.replicate n false) := hmn
  have hm : List.replicate m true ∈ atMostAsMany.leftQuotient (List.replicate m false) :=
    (key m m).2 le_rfl
  have hn : List.replicate n true ∈ atMostAsMany.leftQuotient (List.replicate n false) :=
    (key n n).2 le_rfl
  rw [hmn'] at hm
  rw [← hmn'] at hn
  exact le_antisymm ((key n m).1 hm) ((key m n).1 hn)

/-- The string `trueⁿ falseⁿ`, used in the second item of Exercise `exer:non-rational`. -/
def blockWord (n : ℕ) : List Bool := List.replicate n true ++ List.replicate n false

@[simp] lemma count_true_blockWord (n : ℕ) : (blockWord n).count true = n := by
  simp [blockWord, List.count_append, List.count_replicate]

@[simp] lemma length_blockWord (n : ℕ) : (blockWord n).length = 2 * n := by
  simp [blockWord]; omega

lemma count_true_take_blockWord (k j : ℕ) :
    ((blockWord k).take j).count true = min j k := by
  rw [blockWord, List.take_append, List.take_replicate, List.take_replicate,
    List.length_replicate, List.count_append, List.count_replicate, List.count_replicate]
  simp

/-- The language of the squares `{ u u }` over a two-letter alphabet is not regular. -/
lemma not_isRegular_square :
    ¬ Language.IsRegular ({w : List Bool | ∃ u, w = u ++ u} : Language Bool) := by
  refine not_isRegular_of_leftQuotient_injective blockWord ?_
  intro m n hmn
  have hmn' : Language.leftQuotient ({w : List Bool | ∃ u, w = u ++ u} : Language Bool)
      (blockWord m)
      = Language.leftQuotient ({w : List Bool | ∃ u, w = u ++ u} : Language Bool)
        (blockWord n) := hmn
  have h1 : blockWord n ∈ Language.leftQuotient
      ({w : List Bool | ∃ u, w = u ++ u} : Language Bool) (blockWord n) :=
    ⟨blockWord n, rfl⟩
  rw [← hmn'] at h1
  obtain ⟨u, hu⟩ := h1
  have hlen : u.length = m + n := by
    have h := congrArg List.length hu
    simp at h
    omega
  have htake : (blockWord m ++ blockWord n).take (m + n) = u := by
    rw [hu, ← hlen, List.take_left]
  have hcount : (blockWord m ++ blockWord n).count true = m + n := by
    simp [List.count_append]
  have hu' : (blockWord m ++ blockWord n).count true = 2 * u.count true := by
    rw [hu, List.count_append]; omega
  have htk : u.count true = min (m + n) m + min (m + n - 2 * m) n := by
    rw [← htake, List.take_append, List.count_append, length_blockWord,
      count_true_take_blockWord, count_true_take_blockWord]
  omega

/-! ## Mealy machines and marked strings

The automaton used in the solution of Exercise `exer:mealy-as-restricted-mso-relabelling` to turn
"the output letter produced in the position `x` is `b`" into a regular language of strings marked
at `x`, which `Transducers.MarkLogic.exists_form_of_regular` then turns into an mso formula. -/

section MealyMark

open MarkStr

variable {A B Q : Type}

/-- The `x`-th letter of the output of a Mealy machine is produced by the transition taken after
the prefix of length `x`. -/
lemma mealy_eval_getElem? (M : Mealy A B Q) (w : List A) (x : ℕ) (hx : x < w.length) :
    (M.eval w)[x]? = some (M.step (M.trans (w.take x) M.init) w[x]).2 := by
  have hlen : (M.eval (w.take x)).length = x := by
    simp [Mealy.eval_length]
    omega
  conv_lhs => rw [show w = w.take x ++ w.drop x from (List.take_append_drop x w).symm]
  rw [Mealy.eval_append, List.getElem?_append_right (by omega), hlen]
  rw [List.drop_eq_getElem_cons hx, Mealy.run_cons]
  simp

/-- The transition function of that automaton: it runs the Mealy machine, and as soon as it reads a
marked position it stores the output letter produced there and stops. -/
def mealyMarkStep (M : Mealy A B Q) : Q × Option B → Mark2 A → Q × Option B := fun st z =>
  match st.2 with
  | some b => (st.1, some b)
  | none =>
      if z.2.1 then ((M.step st.1 z.1).1, some (M.step st.1 z.1).2)
      else ((M.step st.1 z.1).1, none)

/-- The automaton accepting the marked strings whose marked position produces the letter `b`. -/
def mealyMarkDFA (M : Mealy A B Q) (b : B) : DFA (Mark2 A) (Q × Option B) where
  step := mealyMarkStep M
  start := (M.init, none)
  accept := {st | st.2 = some b}

lemma mealyMark_frozen (M : Mealy A B Q) (u : List (Mark2 A)) (q : Q) (b : B) :
    strTrans (mealyMarkStep M) u (q, some b) = (q, some b) := by
  induction u with
  | nil => rfl
  | cons z u ih =>
      show strTrans (mealyMarkStep M) u (mealyMarkStep M (q, some b) z) = _
      exact ih

lemma mealyMark_unmarked (M : Mealy A B Q) (u : List A) (q : Q) :
    strTrans (mealyMarkStep M) (unmark2 u) (q, none) = (M.trans u q, none) := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
      show strTrans (mealyMarkStep M) (unmark2 u) (mealyMarkStep M (q, none) (a, false, false)) = _
      rw [show mealyMarkStep M (q, none) (a, false, false) = ((M.step q a).1, none) from rfl, ih]
      rfl

/-- A string marked outside its positions carries no mark at all. -/
lemma markAt2_diag_of_le (w : List A) (x : ℕ) (hx : w.length ≤ x) :
    markAt2 w x x = unmark2 w := by
  refine List.ext_getElem? fun j => ?_
  rw [markAt2_getElem?, unmark2, List.getElem?_map]
  rcases hj : w[j]? with - | a
  · simp
  · have hjl : j < w.length := (List.getElem?_eq_some_iff.1 hj).1
    have hjx : j ≠ x := by omega
    simp [hjx]

/-- The language recognised by the automaton: the string marked at `x` is accepted exactly when the
Mealy machine outputs the letter `b` in the position `x`. -/
lemma mealyMark_accepts (M : Mealy A B Q) (b : B) (w : List A) (x : ℕ) :
    markAt2 w x x ∈ (mealyMarkDFA M b).accepts ↔ (M.eval w)[x]? = some b := by
  have hmem : markAt2 w x x ∈ (mealyMarkDFA M b).accepts ↔
      (strTrans (mealyMarkStep M) (markAt2 w x x) (M.init, none)).2 = some b := Iff.rfl
  rw [hmem]
  by_cases hx : x < w.length
  · rw [markAt2_diag w x hx]
    rw [show strTrans (mealyMarkStep M)
        (unmark2 (w.take x) ++ (w[x], true, true) :: unmark2 (w.drop (x + 1)))
        ((M.init, none) : Q × Option B)
        = strTrans (mealyMarkStep M) ((w[x], true, true) :: unmark2 (w.drop (x + 1)))
            (strTrans (mealyMarkStep M) (unmark2 (w.take x)) ((M.init, none) : Q × Option B)) by
      simp [strTrans, List.foldl_append]]
    rw [mealyMark_unmarked]
    rw [show strTrans (mealyMarkStep M) ((w[x], true, true) :: unmark2 (w.drop (x + 1)))
        ((M.trans (w.take x) M.init, none) : Q × Option B)
        = strTrans (mealyMarkStep M) (unmark2 (w.drop (x + 1)))
            (((M.step (M.trans (w.take x) M.init) w[x]).1,
              some (M.step (M.trans (w.take x) M.init) w[x]).2) : Q × Option B) from rfl]
    rw [mealyMark_frozen, mealy_eval_getElem? M w x hx]
  · rw [markAt2_diag_of_le w x (by omega), mealyMark_unmarked]
    have hxlen : (M.eval w).length ≤ x := by
      rw [Mealy.eval_length]; omega
    simp [List.getElem?_eq_none hxlen]

end MealyMark

/-! ## Running a bimachine from the right

The state of the suffix automaton of a bimachine after a string `w` (`Transducers.BimachIndex.sfx`)
obeys a recursion on the *left* of `w`, because the suffix automaton reads `w` from right to left.
Together with `Transducers.Bimachine.evalFrom_cons` this gives a recursion for the output of a
bimachine that is convenient for computing with explicit bimachines. -/

section Bimachines

variable {A B P S : Type}

@[simp] lemma sfx_nil (M : Bimachine A B P S) : BimachIndex.sfx M [] = M.suffixInit := rfl

lemma sfx_cons (M : Bimachine A B P S) (a : A) (w : List A) :
    BimachIndex.sfx M (a :: w) = M.suffixStep (BimachIndex.sfx M w) a := by
  simp [BimachIndex.sfx, strTrans]

/-- The recursion for the output of a bimachine, with the state of the suffix automaton written
as `Transducers.BimachIndex.sfx`. -/
lemma evalFrom_cons' (M : Bimachine A B P S) (p : P) (a : A) (w : List A) :
    M.evalFrom p (a :: w)
      = M.out p (BimachIndex.sfx M (a :: w)) ++ M.evalFrom (M.prefixStep p a) w :=
  M.evalFrom_cons p a w

end Bimachines

/-! ## Two-letter alphabets for the prime regular functions

The solution to Exercise `exer:two-letter-alphabet-suffices` encodes the letters of a finite
alphabet `A₀` by bit strings.  Instead of the fixed-length code of the book we use the unary
self-delimiting code `code a = 1^{idx a} 0`, which is decoded by a sequential rewriting
(`Transducers.seqEval`) with no need to say anything special about badly formatted inputs: the
decoder simply counts the ones since the last zero, and emits the corresponding letter at every
zero.  A code that is not self-delimiting would need the block structure of the input, and the
statement of the exercise would not become any stronger. -/

namespace TwoLetter

variable {A₀ : Type} [Finite A₀]

/-- The index of a letter of a finite alphabet. -/
noncomputable def idx (a : A₀) : ℕ := (Finite.equivFin A₀ a : Fin (Nat.card A₀))

lemma idx_lt (a : A₀) : idx a < Nat.card A₀ := (Finite.equivFin A₀ a).isLt

@[simp] lemma equivFin_symm_idx (a : A₀) :
    (Finite.equivFin A₀).symm ⟨idx a, idx_lt a⟩ = a := by
  simp [idx]

/-- The unary self-delimiting code of a letter: `idx a` ones followed by a zero. -/
noncomputable def code (a : A₀) : List Bool := List.replicate (idx a) true ++ [false]

/-- The mirror image of the code, used for map reverse. -/
noncomputable def codeRev (a : A₀) : List Bool := (code a).reverse

/-- Counting the ones since the last zero, up to the size of the alphabet. -/
def bump {n : ℕ} (m : Fin (n + 1)) : Fin (n + 1) :=
  if h : (m : ℕ) < n then ⟨m + 1, by omega⟩ else m

/-- The transition function of the decoder. -/
def decStep {n : ℕ} (m : Fin (n + 1)) (b : Bool) : Fin (n + 1) := if b then bump m else 0

/-- The output function of the decoder: at every zero, the letter whose index is the number of
ones that precede it (nothing if there is no such letter). -/
noncomputable def decOut (A₀ : Type) [Finite A₀] (m : Fin (Nat.card A₀ + 1)) (b : Bool) :
    List A₀ :=
  if b then [] else
    if h : (m : ℕ) < Nat.card A₀ then [(Finite.equivFin A₀).symm ⟨m, h⟩] else []

/-- The decoder of a block of bits. -/
noncomputable def decBlock (A₀ : Type) [Finite A₀] (u : List Bool) : List A₀ :=
  seqEval decStep (decOut A₀) 0 u

lemma seqEval_append {A B Mo : Type} (μ : Mo → A → Mo) (ψ : Mo → A → List B) (m : Mo)
    (u v : List A) :
    seqEval μ ψ m (u ++ v) = seqEval μ ψ m u ++ seqEval μ ψ (u.foldl μ m) v := by
  induction u generalizing m with
  | nil => simp
  | cons a u ih => simp [ih, List.append_assoc]

lemma foldl_decStep_trues {n : ℕ} {i : ℕ} (h : i ≤ n) :
    (List.replicate i true).foldl (decStep (n := n)) 0 = ⟨i, by omega⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [List.replicate_succ', List.foldl_append, ih (by omega)]
      have hi : i < n := by omega
      simp [decStep, bump, hi]

lemma seqEval_decOut_trues (m : Fin (Nat.card A₀ + 1)) (i : ℕ) :
    seqEval decStep (decOut A₀) m (List.replicate i true) = [] := by
  induction i generalizing m with
  | zero => rfl
  | succ i ih => rw [List.replicate_succ, seqEval_cons, ih]; simp [decOut]

lemma seqEval_code_append (a : A₀) (v : List Bool) :
    seqEval decStep (decOut A₀) 0 (code a ++ v) = a :: seqEval decStep (decOut A₀) 0 v := by
  have hle : idx a ≤ Nat.card A₀ := le_of_lt (idx_lt a)
  rw [code, List.append_assoc, seqEval_append, seqEval_decOut_trues, foldl_decStep_trues hle]
  have h1 : ([false] ++ v) = false :: v := rfl
  rw [h1, seqEval_cons]
  have h2 : decOut A₀ ⟨idx a, by omega⟩ false = [a] := by
    simp [decOut, idx_lt a]
  have h3 : decStep (n := Nat.card A₀) ⟨idx a, by omega⟩ false = 0 := by simp [decStep]
  rw [h2, h3]
  simp

lemma decBlock_homOf_code (u : List A₀) : decBlock A₀ (homOf code u) = u := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      have h : homOf (code : A₀ → List Bool) (a :: u) = code a ++ homOf code u := by
        simp [homOf]
      rw [decBlock, h, seqEval_code_append]
      exact congrArg (a :: ·) ih

omit [Finite A₀] in
lemma homOf_append (φ : A₀ → List Bool) (x y : List A₀) :
    homOf φ (x ++ y) = homOf φ x ++ homOf φ y := by simp [homOf]

lemma reverse_homOf_codeRev (u : List A₀) :
    (homOf codeRev u).reverse = homOf code u.reverse := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      have h : homOf (codeRev : A₀ → List Bool) (a :: u) = codeRev a ++ homOf codeRev u := by
        simp [homOf]
      rw [h, List.reverse_append, ih, List.reverse_cons, homOf_append]
      simp [codeRev, homOf]

lemma decBlock_dup (u : List A₀) :
    decBlock A₀ (homOf code u ++ homOf code u) = u ++ u := by
  rw [← homOf_append]
  exact decBlock_homOf_code _

lemma decBlock_rev (u : List A₀) :
    decBlock A₀ (homOf codeRev u).reverse = u.reverse := by
  rw [reverse_homOf_codeRev]
  exact decBlock_homOf_code _

/-- Map duplicate over an arbitrary finite alphabet, decomposed into map duplicate over the
two-letter alphabet and two rational functions. -/
lemma mapDuplicate_decomp (w : List (Option A₀)) :
    mapLift (decBlock A₀) (mapDuplicate Bool (mapLift (homOf (code : A₀ → List Bool)) w))
      = mapDuplicate A₀ w := by
  have h1 : mapLift (fun v : List Bool => v ++ v) (mapLift (homOf (code : A₀ → List Bool)) w)
      = mapLift ((fun v : List Bool => v ++ v) ∘ homOf code) w :=
    (congrFun (mapLift_comp' _ _) w).symm
  have h2 : mapLift (decBlock A₀) (mapLift ((fun v : List Bool => v ++ v) ∘ homOf code) w)
      = mapLift (decBlock A₀ ∘ ((fun v : List Bool => v ++ v) ∘ homOf code)) w :=
    (congrFun (mapLift_comp' _ _) w).symm
  have h3 : (decBlock A₀ ∘ ((fun v : List Bool => v ++ v) ∘ homOf (code : A₀ → List Bool)))
      = fun u : List A₀ => u ++ u := funext fun u => decBlock_dup u
  show mapLift (decBlock A₀) (mapLift (fun v : List Bool => v ++ v)
    (mapLift (homOf (code : A₀ → List Bool)) w)) = mapLift (fun u : List A₀ => u ++ u) w
  rw [h1, h2, h3]

/-- Map reverse over an arbitrary finite alphabet, decomposed into map reverse over the
two-letter alphabet and two rational functions. -/
lemma mapReverse_decomp (w : List (Option A₀)) :
    mapLift (decBlock A₀) (mapReverse Bool (mapLift (homOf (codeRev : A₀ → List Bool)) w))
      = mapReverse A₀ w := by
  have h1 : mapLift (List.reverse : List Bool → List Bool)
        (mapLift (homOf (codeRev : A₀ → List Bool)) w)
      = mapLift (List.reverse ∘ homOf codeRev) w :=
    (congrFun (mapLift_comp' _ _) w).symm
  have h2 : mapLift (decBlock A₀) (mapLift (List.reverse ∘ homOf (codeRev : A₀ → List Bool)) w)
      = mapLift (decBlock A₀ ∘ (List.reverse ∘ homOf codeRev)) w :=
    (congrFun (mapLift_comp' _ _) w).symm
  have h3 : (decBlock A₀ ∘ (List.reverse ∘ homOf (codeRev : A₀ → List Bool)))
      = (List.reverse : List A₀ → List A₀) := funext fun u => decBlock_rev u
  show mapLift (decBlock A₀) (mapLift (List.reverse : List Bool → List Bool)
    (mapLift (homOf (codeRev : A₀ → List Bool)) w)) = mapLift List.reverse w
  rw [h1, h2, h3]

lemma isRationalFun_decBlock : IsRationalFun (decBlock A₀) :=
  isRationalFun_seqEval _ _ _

end TwoLetter

/-! ## Finite case distinctions on strings

The solution to Exercise `exer:finite-range-ideals` builds rational functions that replace finitely
many given strings by finitely many other strings.  Such a function is a finite case distinction
over singleton languages, hence rational. -/

/-- A function that agrees with `φ` on a finite set of strings and returns the empty string
elsewhere is rational: it is a finite case distinction over singleton languages. -/
lemma isRationalFun_finsetCases {D A : Type} [Finite D] [Finite A] [DecidableEq D]
    (S : Finset (List D)) (φ : List D → List A) :
    IsRationalFun (fun u => if u ∈ S then φ u else []) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using isRationalFun_const (A := D) (B := A) []
  | insert v S hv ih =>
      have hite := isRationalFun_ite_lang (L := ({v} : Language D)) (isRegular_singleton v)
        (isRationalFun_const (A := D) (B := A) (φ v)) ih
      have heq : (fun u => if u ∈ ({v} : Language D) then φ v else if u ∈ S then φ u else [])
          = fun u => if u ∈ insert v S then φ u else [] := by
        funext u
        by_cases hu : u = v
        · subst hu
          rw [if_pos (Set.mem_singleton_iff.2 rfl), if_pos (Finset.mem_insert_self _ _)]
        · rw [if_neg (fun h => hu (Set.mem_singleton_iff.1 h))]
          by_cases hs : u ∈ S
          · rw [if_pos hs, if_pos (Finset.mem_insert_of_mem hs)]
          · rw [if_neg hs, if_neg (by simp [hu, hs])]
      exact heq ▸ hite

/-! ## Languages recognised by a homomorphism into a finite monoid

The solution to Exercise `ex:recognisable-relations` uses the standard reformulation of
recognisability, which the author recalls in the solution itself: a language is regular exactly
when it is the inverse image of a subset of a finite monoid under a monoid homomorphism.  Both
directions are proved here, since the project does not have the syntactic monoid of a language.

A homomorphism out of a free monoid is described by a plain function together with the two
equations it satisfies, so that no monoid instance has to be put on `List A`. -/

/-- `h` is a monoid homomorphism from the free monoid `A*` into the monoid `M`. -/
def IsWordHom {A M : Type} [Monoid M] (h : List A → M) : Prop :=
  h [] = 1 ∧ ∀ u v, h (u ++ v) = h u * h v

/-- The deterministic automaton whose states are the elements of `M`, which multiplies the current
state by the value of `h` on the letter it reads.  Its accepting states are `F`, so it recognises
the inverse image of `F` under `h`. -/
def homDFA {A M : Type} [Monoid M] (h : List A → M) (F : Set M) : DFA A M where
  step m a := m * h [a]
  start := 1
  accept := F

lemma homDFA_evalFrom {A M : Type} [Monoid M] {h : List A → M} (hh : IsWordHom h) (F : Set M)
    (m : M) (w : List A) : (homDFA h F).evalFrom m w = m * h w := by
  induction w generalizing m with
  | nil => simp [homDFA, DFA.evalFrom, hh.1]
  | cons a w ih =>
      rw [DFA.evalFrom_cons, ih]
      show m * h [a] * h w = _
      rw [mul_assoc, ← hh.2 [a] w]
      rfl

/-- The inverse image of a subset of a finite monoid under a homomorphism is a regular language. -/
lemma isRegular_of_wordHom {A M : Type} [Monoid M] [Fintype M] {h : List A → M}
    (hh : IsWordHom h) (F : Set M) : Language.IsRegular {w | h w ∈ F} := by
  refine ⟨M, inferInstance, homDFA h F, ?_⟩
  ext w
  show (homDFA h F).evalFrom (homDFA h F).start w ∈ (homDFA h F).accept ↔ h w ∈ F
  rw [homDFA_evalFrom hh F]
  show 1 * h w ∈ F ↔ h w ∈ F
  rw [one_mul]

/-- Conversely, every regular language is the inverse image of a subset of a finite monoid under a
homomorphism: the monoid is the transition monoid of a deterministic automaton recognising it,
that is, the opposite of the monoid of maps from states to states, since reading a string
transforms states from the left. -/
lemma exists_wordHom_of_isRegular {A : Type} {L : Language A} (hL : L.IsRegular) :
    ∃ (M : Type) (_ : Monoid M) (_ : Fintype M) (h : List A → M) (F : Set M),
      IsWordHom h ∧ L = {w | h w ∈ F} := by
  obtain ⟨σ, _, D, rfl⟩ := hL
  classical
  letI : Fintype (Function.End σ) := show Fintype (σ → σ) from inferInstance
  letI : Fintype (Function.End σ)ᵐᵒᵖ := Fintype.ofEquiv _ MulOpposite.opEquiv
  refine ⟨(Function.End σ)ᵐᵒᵖ, inferInstance, inferInstance,
    fun w => MulOpposite.op (fun q => D.evalFrom q w), {x | MulOpposite.unop x D.start ∈ D.accept},
    ⟨?_, ?_⟩, ?_⟩
  · apply MulOpposite.unop_injective
    funext q
    simp [DFA.evalFrom]
    rfl
  · intro u v
    apply MulOpposite.unop_injective
    funext q
    show D.evalFrom q (u ++ v) = _
    rw [DFA.evalFrom_of_append]
    rfl
  · rfl

end Exercises
end Transducers
