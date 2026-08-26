/-
The exercises of the introduction of *Transducers* (M. Bojańczyk), i.e. of the
source file `intro.tex`.

Exercises are not numbered results of the book, so they are not listed in
`THEOREMS.md`; they are listed in `EXERCISES.md` instead.  As everywhere else
in this project, an exercise is identified by its LaTeX label, as in
Exercise `exer:reverse-continuous`.

The eleven exercises of the introduction all concern continuity
(Definition `def:continuity`): the first five ask for continuity of concrete
functions, the next three delimit the notion, and the last three compare it
with the metric on strings given by the number of states needed to tell two
strings apart.

Note that inside this file `Continuous` is `Transducers.Continuous`, the
continuity of Definition `def:continuity`; topological continuity is written
`_root_.Continuous`.
-/
import RequestProject.Exercises.IntroAux
import RequestProject.PartC.ContAux

namespace Transducers.Exercises

open scoped Nat

section Introduction

/-! ## Exercise `exer:reverse-continuous` -/

/-- **Exercise `exer:reverse-continuous`.**  The reversal function
`a₁ ⋯ aₙ ↦ aₙ ⋯ a₁` is continuous.

Reversal continuity is also the first half of the book's
Lemma `lem:reversal-duplication-continuous`, which is formalised in `PartC/ContAux.lean`;
rather than restating its proof, the exercise is deduced from it. -/
theorem reverse_continuous {A : Type} : Continuous (List.reverse : List A → List A) :=
  continuous_reverse

/-! ## Exercise `exer:duplication-continuous` -/

/-- **Exercise `exer:duplication-continuous`.**  The duplication function
`w ↦ ww` is continuous.

Duplication continuity is also the second half of the book's
Lemma `lem:reversal-duplication-continuous`, which is formalised in `PartC/ContAux.lean`
by the automaton of the author's solution: besides the state reached from the
initial state, it stores the state transformation of the string read so far. -/
theorem duplication_continuous {A : Type} : Continuous (fun w : List A => w ++ w) :=
  continuous_dup

/-! ## Exercise `exer:squaring-continuous` -/

/-- The dfa recognising `{w | w^{|w|} ∈ M.accepts}`.  After reading `w` its
state is the pair consisting of the state transformation of `w` and of the map
`t ↦ t^{|w|}` on state transformations.  This is the automaton of the author's
solution, with the transformation monoid of the dfa `M` playing the role of the
monoid recognising the output language. -/
def sqDFA {A σ : Type} (M : DFA A σ) : DFA A ((σ → σ) × ((σ → σ) → (σ → σ))) where
  step := fun s a => (fun q => M.step (s.1 q) a, fun t => s.2 t ∘ t)
  start := (id, fun _ => id)
  accept := {s | s.2 s.1 M.start ∈ M.accept}

lemma sqDFA_evalFrom {A σ : Type} (M : DFA A σ) (s : (σ → σ) × ((σ → σ) → (σ → σ)))
    (w : List A) :
    (sqDFA M).evalFrom s w = (fun q => M.evalFrom (s.1 q) w, fun t => s.2 t ∘ t^[w.length]) := by
  induction w generalizing s with
  | nil => simp [DFA.evalFrom]
  | cons a w ih =>
      rw [DFA.evalFrom_cons, ih]
      simp only [sqDFA, List.length_cons, Prod.mk.injEq]
      refine ⟨rfl, funext fun t => ?_⟩
      rw [Function.iterate_succ']
      rfl

/-- **Exercise `exer:squaring-continuous`.**  The squaring function
`w ↦ w^{|w|}` is continuous. -/
theorem squaring_continuous {A : Type} : Continuous (fun w : List A => npow w w.length) := by
  classical
  rintro L ⟨σ, hσ, M, rfl⟩
  refine ⟨(σ → σ) × ((σ → σ) → (σ → σ)), inferInstance, sqDFA M, ?_⟩
  ext w
  simp only [DFA.mem_accepts, DFA.eval, sqDFA_evalFrom]
  show _ ∈ (sqDFA M).accept ↔ _
  simp only [sqDFA, Set.mem_setOf_eq, evalFrom_npow, Function.comp_apply, id]
  exact Iff.rfl

/-! ## Exercise `exer:factorial-power-continuous` and Exercise `exer:factorial-continuous` -/

/-- The exponents `g(n)!` stabilise, uniformly in the state transformation:
for a non-decreasing `g` there is an `n₀` such that `t^[(g n)!] = t^[(g n₀)!]`
for every `n ≥ n₀` and every self-map `t` of the (finite) state set.

This is the claim of the author's solution to Exercise
`exer:factorial-power-continuous` ("factorial powers in a monoid must
necessarily stabilise"), in the transformation monoid of a dfa. -/
lemma exists_exponent_stable (S : Type) [Finite S] (g : ℕ → ℕ) (hg : Monotone g) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ t : S → S, t^[(g n)!] = t^[(g n₀)!] := by
  obtain ⟨D, hD, hstab⟩ := iterate_stable_uniform S
  set c : ℕ → ℕ := fun n => min (g n) D with hc
  have hbdd : BddAbove (Set.range c) := ⟨D, by rintro _ ⟨n, rfl⟩; exact min_le_right _ _⟩
  obtain ⟨n₀, hn₀⟩ : sSup (Set.range c) ∈ Set.range c := Nat.sSup_mem ⟨c 0, ⟨0, rfl⟩⟩ hbdd
  refine ⟨n₀, fun n hn t => ?_⟩
  have hcn : c n = c n₀ := by
    have h1 : c n ≤ sSup (Set.range c) := le_csSup hbdd ⟨n, rfl⟩
    have h2 : c n₀ ≤ c n := by have := hg hn; simp only [hc]; omega
    rw [← hn₀] at h1; omega
  by_cases hlt : g n₀ < D
  · have hgn : g n = g n₀ := by simp only [hc] at hcn; omega
    rw [hgn]
  · push_neg at hlt
    have hgn : D ≤ g n := by simp only [hc] at hcn; omega
    have key : ∀ m, D ≤ g m → t^[(g m)!] = t^[D] := fun m hm =>
      hstab t _ (le_trans hm (Nat.self_le_factorial _)) (Nat.dvd_factorial hD hm)
    rw [key n hgn, key n₀ hlt]

/-- The dfa recognising `{w | w^{g(|w|)!} ∈ M.accepts}`, where `n₀` is the
stabilisation threshold of `exists_exponent_stable`.  Its state after reading
`w` is the state transformation of `w` together with the length of `w`, capped
at `n₀`. -/
def facDFA {A σ : Type} (M : DFA A σ) (g : ℕ → ℕ) (n₀ : ℕ) :
    DFA A ((σ → σ) × Fin (n₀ + 1)) where
  step := fun s a => (fun q => M.step (s.1 q) a, ⟨min (s.2.val + 1) n₀, by omega⟩)
  start := (id, ⟨0, by omega⟩)
  accept := {s | (s.1)^[(g s.2.val)!] M.start ∈ M.accept}

lemma facDFA_evalFrom {A σ : Type} (M : DFA A σ) (g : ℕ → ℕ) (n₀ : ℕ)
    (f : σ → σ) (j : Fin (n₀ + 1)) (w : List A) :
    (facDFA M g n₀).evalFrom (f, j) w
      = (fun q => M.evalFrom (f q) w, ⟨min (j.val + w.length) n₀, by omega⟩) := by
  induction w generalizing f j with
  | nil =>
      simp only [DFA.evalFrom_nil, List.length_nil, Nat.add_zero, Prod.mk.injEq]
      exact ⟨trivial, Fin.ext (by simp [Nat.min_eq_left (Nat.lt_succ_iff.mp j.isLt)])⟩
  | cons a w ih =>
      rw [DFA.evalFrom_cons]
      show (facDFA M g n₀).evalFrom (_, _) w = _
      rw [ih]
      simp only [List.length_cons, Prod.mk.injEq]
      exact ⟨rfl, Fin.ext (by simp; omega)⟩

/-- **Exercise `exer:factorial-power-continuous`.**  For every non-decreasing
`g : ℕ → ℕ`, possibly non-computable, the function `w ↦ w^{g(|w|)!}` is
continuous. -/
theorem factorial_power_continuous {A : Type} (g : ℕ → ℕ) (hg : Monotone g) :
    Continuous (fun w : List A => npow w (g w.length)!) := by
  classical
  rintro L ⟨σ, hσ, M, rfl⟩
  obtain ⟨n₀, hn₀⟩ := exists_exponent_stable σ g hg
  refine ⟨(σ → σ) × Fin (n₀ + 1), inferInstance, facDFA M g n₀, ?_⟩
  ext w
  simp only [DFA.mem_accepts, DFA.eval]
  show (facDFA M g n₀).evalFrom ((id : σ → σ), (⟨0, by omega⟩ : Fin (n₀ + 1))) w ∈ _ ↔ _
  rw [facDFA_evalFrom]
  show _ ∈ (facDFA M g n₀).accept ↔ _
  simp only [facDFA, Set.mem_setOf_eq, id, Nat.zero_add]
  show (fun q => M.evalFrom q w)^[(g (min w.length n₀))!] M.start ∈ M.accept ↔
      M.evalFrom M.start (npow w (g w.length)!) ∈ M.accept
  rw [evalFrom_npow]
  by_cases h : w.length ≤ n₀
  · rw [min_eq_left h]
  · push_neg at h
    rw [min_eq_right (le_of_lt h), hn₀ w.length (le_of_lt h)]

/-- **Exercise `exer:factorial-continuous`.**  The factorial function
`w ↦ w^{|w|!}` is continuous.

The author's solution builds a third component `m ↦ m^{|w|!}` on top of the
automaton of Exercise `exer:squaring-continuous`; here the exercise is instead
deduced from the next one, Exercise `exer:factorial-power-continuous`, of which
it is the case `g = id`.  (Incidentally, the update rule given for that third
component in the book -- multiply the old value coordinatewise by the new
second component -- computes `m ↦ m^{|w|! + |w|}` rather than `m ↦ m^{|w|!}`;
the correct rule composes the two, `ψ' = φ' ∘ ψ`.) -/
theorem factorial_continuous {A : Type} : Continuous (fun w : List A => npow w w.length !) :=
  factorial_power_continuous (A := A) id monotone_id

/-! ## Exercise `ex:continuity-for-finite-images` -/

/-- **Exercise `ex:continuity-for-finite-images`.**  A string-to-string
function with finitely many output values is continuous if and only if the
inverse image of each output value is regular.

The inverse image of a value that is not attained is empty, hence regular, so
the condition may be quantified over all output strings. -/
theorem continuous_iff_regular_fibers {A B : Type} (f : List A → List B)
    (hfin : (Set.range f).Finite) :
    Continuous f ↔ ∀ v : List B, Language.IsRegular ({w : List A | f w = v} : Language A) := by
  classical
  constructor
  · intro hf v
    exact hf _ (isRegular_singleton v)
  · intro hfib L hL
    set l : List (List B) := hfin.toFinset.toList with hl
    set P : List B → Language A :=
      fun v => if v ∈ L then ({w : List A | f w = v} : Language A) else 0 with hP
    have hmemP : ∀ (v : List B) (x : List A), x ∈ P v ↔ (v ∈ L ∧ f x = v) := by
      intro v x
      by_cases hv : v ∈ L
      · simp only [hP, if_pos hv]
        exact ⟨fun hx => ⟨hv, hx⟩, fun hx => hx.2⟩
      · simp only [hP, if_neg hv]
        exact ⟨fun hx => hx.elim, fun hx => absurd hx.1 hv⟩
    have hEq : ({w : List A | f w ∈ L} : Language A) = unionOf P l := by
      ext x
      rw [mem_unionOf]
      constructor
      · intro hx
        refine ⟨f x, ?_, (hmemP (f x) x).2 ⟨hx, rfl⟩⟩
        simp only [hl, Finset.mem_toList, Set.Finite.mem_toFinset]
        exact ⟨x, rfl⟩
      · rintro ⟨v, -, hx⟩
        obtain ⟨hv, hfx⟩ := (hmemP v x).1 hx
        show f x ∈ L
        rw [hfx]
        exact hv
    rw [hEq]
    refine isRegular_unionOf P l (fun v _ => ?_)
    by_cases hv : v ∈ L
    · simp only [hP, if_pos hv]
      exact hfib v
    · simp only [hP, if_neg hv]
      exact isRegular_zero

/-! ## Exercise `exer:middle-letter-not-continuous` -/

/-- The middle letter function: the empty output on inputs of even length, and
the one-letter string consisting of the middle letter of the input otherwise. -/
def middleLetter {A : Type} (w : List A) : List A :=
  if w.length % 2 = 1 then (w.drop (w.length / 2)).take 1 else []

lemma middleLetter_replicate_eq {A : Type} (a b : A) (n : ℕ) :
    middleLetter (List.replicate n b ++ a :: List.replicate n b) = [a] := by
  have hlen : (List.replicate n b ++ a :: List.replicate n b).length = 2 * n + 1 := by
    simp; omega
  rw [middleLetter, hlen, if_pos (by omega : (2 * n + 1) % 2 = 1),
    show (2 * n + 1) / 2 = n by omega, List.drop_append]
  simp

lemma middleLetter_replicate_ne {A : Type} (a b : A) (n j : ℕ) (hj : 0 < j) :
    middleLetter (List.replicate (n + 2 * j) b ++ a :: List.replicate n b) = [b] := by
  have hlen : (List.replicate (n + 2 * j) b ++ a :: List.replicate n b).length
      = 2 * (n + j) + 1 := by simp; omega
  rw [middleLetter, hlen, if_pos (by omega : (2 * (n + j) + 1) % 2 = 1),
    show (2 * (n + j) + 1) / 2 = n + j by omega, List.drop_append, List.drop_replicate,
    List.length_replicate, show n + j - (n + 2 * j) = 0 by omega,
    show n + 2 * j - (n + j) = j by omega]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp [List.replicate_succ]

/-- The language of the strings of odd length whose middle letter is `a` is not
regular.  This is the pumping lemma argument of the author's solution: pumping
a factor of `bⁿ a bⁿ` inside its prefix `bⁿ` moves the middle letter into the
block of `b`s. -/
lemma middleLang_not_isRegular {A : Type} {a b : A} (hab : a ≠ b) :
    ¬ Language.IsRegular ({w : List A | middleLetter w = [a]} : Language A) := by
  rintro ⟨σ, hσ, M, hM⟩
  set n := max (Fintype.card σ) 1 with hn
  set x := List.replicate n b ++ a :: List.replicate n b with hxdef
  have hx : x ∈ M.accepts := by rw [hM]; exact middleLetter_replicate_eq a b n
  have hlenx : x.length = 2 * n + 1 := by simp [hxdef]; omega
  have hcard : Fintype.card σ ≤ x.length := by rw [hlenx]; omega
  obtain ⟨p, q, r, hxeq, hpq, hqne, hsub⟩ := M.pumping_lemma hx hcard
  set m := p.length + q.length with hm
  have hmn : m ≤ n := le_trans hpq (le_max_left _ _)
  have hx2 : x = (p ++ q) ++ r := by rw [hxeq, List.append_assoc]
  have hpqlen : (p ++ q).length = m := by simp [hm]
  have htake : p ++ q = List.replicate m b := by
    have h1 : p ++ q = x.take m := by rw [hx2, ← hpqlen, List.take_left]
    rw [h1, hxdef, List.take_append, List.take_replicate,
      show m - (List.replicate n b).length = 0 by simp; omega]
    simp [Nat.min_eq_left hmn]
  have hr : r = List.replicate (n - m) b ++ a :: List.replicate n b := by
    have h1 : r = x.drop m := by rw [hx2, ← hpqlen, List.drop_left]
    rw [h1, hxdef, List.drop_append, List.drop_replicate,
      List.length_replicate, show m - n = 0 by omega]
    simp
  obtain ⟨j, hj0, hqj⟩ : ∃ j, 0 < j ∧ q = List.replicate j b := by
    refine ⟨q.length, List.length_pos_iff.2 hqne, List.eq_replicate_iff.2 ⟨rfl, fun z hz => ?_⟩⟩
    have hmem : z ∈ p ++ q := List.mem_append_right _ hz
    rw [htake] at hmem
    exact List.eq_of_mem_replicate hmem
  have hjm : j ≤ m := by rw [hm, hqj]; simp
  have hmem : p ++ (q ++ q ++ q) ++ r ∈ M.accepts := by
    apply hsub
    refine ⟨p ++ (q ++ q ++ q), ⟨p, rfl, q ++ q ++ q, ?_, rfl⟩, r, rfl, rfl⟩
    exact Language.mem_kstar.2 ⟨[q, q, q], by simp, by intro y hy; simp at hy; subst hy; rfl⟩
  have hy : p ++ (q ++ q ++ q) ++ r
      = List.replicate (n + 2 * j) b ++ a :: List.replicate n b := by
    have hassoc : p ++ (q ++ q ++ q) ++ r = (p ++ q) ++ q ++ q ++ r := by simp
    rw [hassoc, htake, hqj, hr]
    simp only [← List.append_assoc, ← List.replicate_add]
    congr 2
    omega
  rw [hM, hy] at hmem
  have hb := middleLetter_replicate_ne a b n j hj0
  have hcon : [b] = [a] := by rw [← hb]; exact hmem
  exact hab (by injection hcon with h; exact h.symm)

/-- **Exercise `exer:middle-letter-not-continuous`.**  The middle letter
function is not continuous as soon as the alphabet has at least two letters. -/
theorem middleLetter_not_continuous {A : Type} {a b : A} (hab : a ≠ b) :
    ¬ Continuous (middleLetter : List A → List A) := by
  intro hf
  exact middleLang_not_isRegular hab (hf _ (isRegular_singleton [a]))

/-! ## Exercise `exer:finite-images-assumption-necessary` -/

/-- The language of the strings that begin with the letter `a`. -/
def headLang {A : Type} (a : A) : Language A := {w : List A | w.head? = some a}

lemma isRegular_headLang {A : Type} (a : A) : (headLang a).IsRegular := by
  classical
  rw [Language.isRegular_iff_finite_range_leftQuotient]
  refine Set.Finite.subset
    (Set.Finite.insert (headLang a) (Set.Finite.insert (Set.univ : Language A)
      (Set.finite_singleton (0 : Language A)))) ?_
  rintro _ ⟨u, rfl⟩
  match u with
  | [] =>
      refine Or.inl ?_
      ext x
      simp only [Language.mem_leftQuotient, List.nil_append]
  | c :: u =>
      by_cases hc : c = a
      · refine Or.inr (Or.inl ?_)
        ext x
        simp only [hc]
        exact ⟨fun _ => Set.mem_univ x, fun _ => rfl⟩
      · refine Or.inr (Or.inr ?_)
        simp only [Set.mem_singleton_iff]
        ext x
        exact ⟨fun h => absurd (by injection h) hc, fun h => h.elim⟩

/-- **Exercise `exer:finite-images-assumption-necessary`.**  The assumption
that there are finitely many output values in Exercise
`ex:continuity-for-finite-images` is necessary: as soon as the alphabet has two
letters there is an injective function, hence one whose inverse images of
single output values are all regular (being empty or singletons), which is not
continuous.

The function is the one of the author's solution: mark the input string with a
letter recording whether its middle letter is `a`, and copy the input after the
mark. -/
theorem exists_regular_fibers_not_continuous {A : Type} {a b : A} (hab : a ≠ b) :
    ∃ f : List A → List A, Function.Injective f ∧
      (∀ v : List A, Language.IsRegular ({w : List A | f w = v} : Language A)) ∧
      ¬ Continuous f := by
  classical
  refine ⟨fun w => (if middleLetter w = [a] then a else b) :: w, ?_, ?_, ?_⟩
  · intro w w' h
    simpa using congrArg List.tail h
  · intro v
    refine isRegular_of_subsingleton (fun x hx y hy => ?_)
    have hx' : (if middleLetter x = [a] then a else b) :: x = v := hx
    have hy' : (if middleLetter y = [a] then a else b) :: y = v := hy
    have : (if middleLetter x = [a] then a else b) :: x
        = (if middleLetter y = [a] then a else b) :: y := by rw [hx', hy']
    simpa using congrArg List.tail this
  · intro hf
    have hreg := hf _ (isRegular_headLang a)
    refine middleLang_not_isRegular hab ?_
    have hEq : ({w : List A | (if middleLetter w = [a] then a else b) :: w ∈ headLang a}
        : Language A) = ({w : List A | middleLetter w = [a]} : Language A) := by
      ext w
      constructor
      · intro hw
        by_cases h : middleLetter w = [a]
        · exact h
        · exfalso
          have hb : ((if middleLetter w = [a] then a else b) :: w).head? = some a := hw
          rw [if_neg h] at hb
          have hba : b = a := by simpa using hb
          exact hab hba.symm
      · intro hw
        have hw' : middleLetter w = [a] := hw
        show ((if middleLetter w = [a] then a else b) :: w).head? = some a
        rw [if_pos hw']
        rfl
    rw [hEq] at hreg
    exact hreg

/-! ## Exercise `ex:distance` -/

/-- The numbers of states of a dfa that accepts `w` but not `w'`. -/
def sepSet {A : Type} (w w' : List A) : Set ℕ :=
  {n : ℕ | ∃ M : DFA A (Fin n), w ∈ M.accepts ∧ w' ∉ M.accepts}

/-- The minimal number of states in a dfa that accepts `w` but not `w'`, which
is `0` when there is no such dfa, i.e. exactly when `w = w'`. -/
noncomputable def sepStates {A : Type} (w w' : List A) : ℕ := sInf (sepSet w w')

open scoped Classical in
/-- **The distance of Exercise `ex:distance`.**  The distance between two
strings is zero if they are equal, and otherwise the reciprocal of the minimal
number of states in a dfa that accepts one of them but not the other. -/
noncomputable def strDist {A : Type} (w w' : List A) : ℝ :=
  if w = w' then 0 else 1 / (sepStates w w' : ℝ)

section Distance

variable {A : Type}

lemma sepSet_comm (w w' : List A) : sepSet w w' = sepSet w' w := by
  have key : ∀ u v : List A, sepSet u v ⊆ sepSet v u := by
    rintro u v n ⟨M, h1, h2⟩
    exact ⟨dfaCompl M, h2, fun h => h h1⟩
  exact Set.Subset.antisymm (key w w') (key w' w)

lemma zero_not_mem_sepSet (w w' : List A) : 0 ∉ sepSet w w' := by
  rintro ⟨M, -, -⟩
  exact M.start.elim0

/-- Two distinct strings are separated by some dfa: the dfa recognising the
singleton language of the first one. -/
lemma sepSet_nonempty {w w' : List A} (h : w ≠ w') : (sepSet w w').Nonempty := by
  obtain ⟨n, M, hM⟩ := exists_fin_dfa (isRegular_singleton w)
  refine ⟨n, M, ?_, ?_⟩
  · rw [hM]; rfl
  · rw [hM]; exact fun hc => h hc.symm

lemma sepStates_mem {w w' : List A} (h : w ≠ w') : sepStates w w' ∈ sepSet w w' :=
  Nat.sInf_mem (sepSet_nonempty h)

lemma sepStates_pos {w w' : List A} (h : w ≠ w') : 0 < sepStates w w' := by
  rcases Nat.eq_zero_or_pos (sepStates w w') with h0 | h0
  · exact absurd (h0 ▸ sepStates_mem h) (zero_not_mem_sepSet w w')
  · exact h0

lemma sepStates_comm (w w' : List A) : sepStates w w' = sepStates w' w := by
  rw [sepStates, sepStates, sepSet_comm]

lemma sepStates_le {w w' : List A} {k : ℕ} (M : DFA A (Fin k))
    (h1 : w ∈ M.accepts) (h2 : w' ∉ M.accepts) : sepStates w w' ≤ k :=
  Nat.sInf_le ⟨M, h1, h2⟩

/-- No dfa with fewer states than `sepStates w w'` tells `w` from `w'`. -/
lemma not_separated {w w' : List A} {k : ℕ} (hk : k < sepStates w w') (M : DFA A (Fin k)) :
    (w ∈ M.accepts ↔ w' ∈ M.accepts) := by
  by_cases hww : w = w'
  · rw [hww]
  · constructor
    · intro h1
      by_contra h2
      exact absurd (sepStates_le M h1 h2) (by omega)
    · intro h1
      by_contra h2
      have hle : sepStates w' w ≤ k := sepStates_le M h1 h2
      rw [sepStates_comm] at hle
      omega

lemma strDist_self (w : List A) : strDist w w = 0 := by simp [strDist]

lemma strDist_of_ne {w w' : List A} (h : w ≠ w') :
    strDist w w' = 1 / (sepStates w w' : ℝ) := by simp [strDist, h]

lemma strDist_nonneg (w w' : List A) : 0 ≤ strDist w w' := by
  by_cases h : w = w'
  · simp [h, strDist_self]
  · rw [strDist_of_ne h]; positivity

lemma strDist_eq_zero_iff {w w' : List A} : strDist w w' = 0 ↔ w = w' := by
  constructor
  · intro h
    by_contra hne
    rw [strDist_of_ne hne] at h
    have hpos : (0:ℝ) < 1 / (sepStates w w' : ℝ) := by
      apply div_pos one_pos
      exact_mod_cast sepStates_pos hne
    linarith
  · rintro rfl; exact strDist_self w

lemma strDist_comm (w w' : List A) : strDist w w' = strDist w' w := by
  by_cases h : w = w'
  · rw [h]
  · rw [strDist_of_ne h, strDist_of_ne (Ne.symm h), sepStates_comm]

/-- **Exercise `ex:distance`, the stronger inequality of the author's
solution.**  The distance is an ultrametric: `d(w₁,w₃) ≤ max (d(w₁,w₂),
d(w₂,w₃))`, because a dfa that tells `w₁` from `w₃` must also tell `w₁` from
`w₂` or `w₂` from `w₃`. -/
theorem strDist_ultrametric (w₁ w₂ w₃ : List A) :
    strDist w₁ w₃ ≤ max (strDist w₁ w₂) (strDist w₂ w₃) := by
  by_cases h13 : w₁ = w₃
  · rw [h13, strDist_self]
    exact le_max_of_le_left (strDist_nonneg _ _)
  by_cases h12 : w₁ = w₂
  · rw [← h12] at *
    exact le_max_right _ _
  by_cases h23 : w₂ = w₃
  · rw [h23] at *
    exact le_max_left _ _
  obtain ⟨M, hM1, hM3⟩ := sepStates_mem h13
  rw [strDist_of_ne h13, strDist_of_ne h12, strDist_of_ne h23]
  by_cases hM2 : w₂ ∈ M.accepts
  · refine le_trans ?_ (le_max_right _ _)
    apply one_div_le_one_div_of_le
    · exact_mod_cast sepStates_pos h23
    · exact_mod_cast sepStates_le M hM2 hM3
  · refine le_trans ?_ (le_max_left _ _)
    apply one_div_le_one_div_of_le
    · exact_mod_cast sepStates_pos h12
    · exact_mod_cast sepStates_le M hM1 hM2

/-- **Exercise `ex:distance`.**  The function `strDist` is indeed a distance on
strings: it is nonnegative, vanishes exactly on equal strings, is symmetric,
and satisfies the triangle inequality (which follows from the ultrametric
inequality of `strDist_ultrametric`). -/
theorem strDist_isMetric :
    (∀ w : List A, strDist w w = 0) ∧
    (∀ w w' : List A, 0 ≤ strDist w w') ∧
    (∀ w w' : List A, strDist w w' = 0 → w = w') ∧
    (∀ w w' : List A, strDist w w' = strDist w' w) ∧
    (∀ w₁ w₂ w₃ : List A, strDist w₁ w₃ ≤ strDist w₁ w₂ + strDist w₂ w₃) := by
  refine ⟨strDist_self, strDist_nonneg, fun w w' h => strDist_eq_zero_iff.1 h, strDist_comm,
    fun w₁ w₂ w₃ => le_trans (strDist_ultrametric w₁ w₂ w₃) ?_⟩
  rcases max_cases (strDist w₁ w₂) (strDist w₂ w₃) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    linarith [strDist_nonneg w₁ w₂, strDist_nonneg w₂ w₃]

/-- The metric space of strings given by Exercise `ex:distance`. -/
noncomputable def strMetric (A : Type) : MetricSpace (List A) where
  dist := strDist
  dist_self := strDist_self
  dist_comm := strDist_comm
  dist_triangle := strDist_isMetric.2.2.2.2
  eq_of_dist_eq_zero := fun {_ _} h => strDist_eq_zero_iff.1 h

/-! ### The distance and the separating automata -/

/-- If no dfa with at most `m` states tells `w` from `w'`, then the two strings
are at distance at most `1/(m+1)`. -/
lemma strDist_le_of_not_separated {w w' : List A} {m : ℕ}
    (h : ∀ j ≤ m, ∀ M : DFA A (Fin j), (w ∈ M.accepts ↔ w' ∈ M.accepts)) :
    strDist w w' ≤ 1 / ((m : ℝ) + 1) := by
  by_cases hww : w = w'
  · rw [hww, strDist_self]; positivity
  · rw [strDist_of_ne hww]
    obtain ⟨M, h1, h2⟩ := sepStates_mem hww
    have hgt : m < sepStates w w' := by
      by_contra hle
      push_neg at hle
      exact h2 ((h _ hle M).1 h1)
    have hcast : ((m : ℝ) + 1) ≤ (sepStates w w' : ℝ) := by exact_mod_cast hgt
    exact one_div_le_one_div_of_le (by positivity) hcast

/-- Conversely, two strings at distance less than `1/k` are not told apart by
any dfa with at most `k` states. -/
lemma not_separated_of_strDist_lt {w w' : List A} {k j : ℕ} (hj : j ≤ k)
    (h : strDist w w' < 1 / (k : ℝ)) (M : DFA A (Fin j)) :
    (w ∈ M.accepts ↔ w' ∈ M.accepts) := by
  by_cases hww : w = w'
  · rw [hww]
  · rw [strDist_of_ne hww] at h
    have hs : (0:ℝ) < (sepStates w w' : ℝ) := by exact_mod_cast sepStates_pos hww
    have hk : (0:ℝ) < (k : ℝ) := by
      by_contra hk0
      push_neg at hk0
      have hk1 : (k : ℝ) = 0 := le_antisymm hk0 (Nat.cast_nonneg k)
      rw [hk1] at h
      simp only [div_zero] at h
      have : (0:ℝ) < 1 / (sepStates w w' : ℝ) := by positivity
      linarith
    have hlt : k < sepStates w w' := by
      have : (k : ℝ) < (sepStates w w' : ℝ) := (one_div_lt_one_div hs hk).mp h
      exact_mod_cast this
    exact not_separated (lt_of_le_of_lt hj hlt) M

end Distance

section Metric

attribute [local instance] strMetric

variable {A B : Type}

lemma dist_eq_strDist (w w' : List A) : dist w w' = strDist w w' := rfl

/-- Around every string there is a ball that contains no other string: the one
of radius `1/(N+1)`, where `N` is the number of states of a dfa recognising the
singleton language of that string. -/
lemma exists_sep_bound (w : List A) :
    ∃ N : ℕ, 0 < N ∧ ∀ w' : List A, w' ≠ w → sepStates w' w ≤ N := by
  obtain ⟨n, M, hM⟩ := exists_fin_dfa (isRegular_singleton w)
  refine ⟨n, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | h
    · exact M.start.elim0
    · exact h
  · intro w' hne
    rw [sepStates_comm]
    refine sepStates_le M ?_ ?_
    · rw [hM]; rfl
    · rw [hM]; exact fun hc => hne hc

/-! ## Exercise `exer:all-functions-continuous-for-metric` -/

/-- **Exercise `exer:all-functions-continuous-for-metric`.**  Every
string-to-string function is continuous with respect to the distance of
Exercise `ex:distance`.

As in the topological description of the author's solution, the reason is that
the distance induces the discrete topology: a small enough ball around a string
is the singleton of that string, because a dfa recognising that singleton tells
it from every other string. -/
theorem strDist_all_continuous (f : List A → List B) : _root_.Continuous f := by
  have hdisc : DiscreteTopology (List A) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro w
    rw [Metric.isOpen_singleton_iff]
    obtain ⟨N, hN0, hN⟩ := exists_sep_bound w
    refine ⟨1 / ((N : ℝ) + 1), by positivity, ?_⟩
    intro y hy
    by_contra hne
    rw [dist_eq_strDist, strDist_of_ne hne] at hy
    have h1 : (sepStates y w : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN y hne
    have h2 : (0:ℝ) < (sepStates y w : ℝ) := by exact_mod_cast sepStates_pos hne
    have h3 : 1 / ((N:ℝ) + 1) < 1 / (sepStates y w : ℝ) :=
      one_div_lt_one_div_of_lt h2 (by linarith)
    linarith
  exact continuous_of_discreteTopology

/-! ## Exercise `exer:continuous-iff-uniformly-continuous` -/

/-- **Exercise `exer:continuous-iff-uniformly-continuous`.**  The continuous
functions in the sense of Definition `def:continuity` are exactly the uniformly
continuous ones for the distance of Exercise `ex:distance`.

Both alphabets are assumed finite, as they are everywhere in the book: the
author's solution counts the automata with a given number of states over a
given alphabet, and that number is finite only for a finite alphabet.

The proof follows the solution.  For the forward implication, the inverse image
of the language of each of the finitely many dfas with at most `n` states over
the output alphabet is regular, hence recognised by a dfa over the input
alphabet, and `1/(m+1)` is a suitable `δ` for `m` the largest of their numbers
of states.  For the backward implication, the strings that no dfa with at most
`m` states tells apart have the same image under the left quotient of the
inverse image, and there are finitely many such classes. -/
theorem continuous_iff_uniformContinuous [Finite A] [Finite B]
    (f : List A → List B) : Continuous f ↔ UniformContinuous f := by
  classical
  constructor
  · intro hcont
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / ((n:ℝ) + 1) < ε := exists_nat_one_div_lt hε
    have hreg : ∀ D : (Σ j : Fin (n+1), DFA B (Fin j)), ∃ k : ℕ, ∃ K : DFA A (Fin k),
        K.accepts = {w : List A | f w ∈ D.2.accepts} :=
      fun D => exists_fin_dfa (hcont _ ⟨Fin D.1, inferInstance, D.2, rfl⟩)
    choose kD KD hKD using hreg
    haveI : Fintype (Σ j : Fin (n+1), DFA B (Fin j)) := Fintype.ofFinite _
    refine ⟨1 / (((Finset.univ.sup kD) : ℕ) + 1 : ℝ), by positivity, ?_⟩
    intro w w' hww
    have hstepB : ∀ j ≤ n, ∀ M : DFA B (Fin j), (f w ∈ M.accepts ↔ f w' ∈ M.accepts) := by
      intro j hj M
      set D : (Σ j : Fin (n+1), DFA B (Fin j)) := ⟨⟨j, by omega⟩, M⟩ with hD
      have h1 : kD D ≤ Finset.univ.sup kD := Finset.le_sup (Finset.mem_univ D)
      have hcast : strDist w w' < 1 / ((Finset.univ.sup kD + 1 : ℕ) : ℝ) := by
        rw [dist_eq_strDist] at hww
        push_cast
        exact hww
      have h2 : w ∈ (KD D).accepts ↔ w' ∈ (KD D).accepts :=
        not_separated_of_strDist_lt (by omega) hcast (KD D)
      rw [hKD D] at h2
      exact h2
    rw [dist_eq_strDist]
    exact lt_of_le_of_lt (strDist_le_of_not_separated hstepB) hn
  · intro hu L hL
    obtain ⟨n, N, hN⟩ := exists_fin_dfa hL
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exact N.start.elim0
      · exact h
    rw [Metric.uniformContinuous_iff] at hu
    obtain ⟨δ, hδ, hu'⟩ := hu (1 / (n:ℝ)) (by positivity)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 / ((m:ℝ) + 1) < δ := exists_nat_one_div_lt hδ
    rw [Language.isRegular_iff_finite_range_leftQuotient]
    refine finite_range_of_factors _
      (fun u => (fun D : (Σ j : Fin (m+1), DFA A (Fin j)) => u ∈ (D.2).accepts)) ?_ ?_
    · exact Set.toFinite _
    · intro u u' hprof
      ext v
      show f (u ++ v) ∈ L ↔ f (u' ++ v) ∈ L
      have hstep : ∀ j ≤ m, ∀ M : DFA A (Fin j),
          ((u ++ v) ∈ M.accepts ↔ (u' ++ v) ∈ M.accepts) := by
        intro j hj M
        have hc := congrFun hprof ⟨⟨j, by omega⟩, accDFA M v⟩
        rw [← mem_accDFA M v, ← mem_accDFA M v]
        exact iff_of_eq hc
      have hd : strDist (u ++ v) (u' ++ v) ≤ 1 / ((m:ℝ) + 1) :=
        strDist_le_of_not_separated hstep
      have hlt : dist (u ++ v) (u' ++ v) < δ := by
        rw [dist_eq_strDist]; exact lt_of_le_of_lt hd hm
      have hout : dist (f (u ++ v)) (f (u' ++ v)) < 1 / (n:ℝ) := hu' hlt
      rw [dist_eq_strDist] at hout
      rw [← hN]
      exact not_separated_of_strDist_lt (le_refl n) hout N

end Metric

end Introduction

end Transducers.Exercises
