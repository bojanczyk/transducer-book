/-
Exercises of Part D, Section *Evaluation* (`partDPolyregular/evaluation.tex`): the four exercises
about monoids.

* Exercise `exer:monoid-vs-deterministic-automaton` -- the monoid recognising a language can be
  exponentially bigger than a deterministic automaton
  (`Transducers.Exercises.monoid_vs_deterministic_automaton`);
* Exercise `exer:monoid-vs-deterministic-automaton-strengthened` -- the same, with deterministic
  automata reading from left to right *and* from right to left
  (`Transducers.Exercises.monoid_vs_deterministic_automaton_strengthened`);
* Exercise `exer:idempotents-in-monoid-of-functions` -- the idempotents of the monoid of functions
  `Q → Q` (`Transducers.Exercises.idempotent_function_iff`);
* Exercise `exer:idempotents-in-monoid-of-relations` -- the idempotents of the monoid of binary
  relations on `Q` (`Transducers.Exercises.idempotent_relation_iff`,
  `Transducers.Exercises.idempotent_relation_iff_of_finite`).

As in Theorem `thm:monoids-equal-automata` (`Transducers.regular_iff_recognised_by_monoid`), a
language `L ⊆ A*` is *recognised* by a monoid homomorphism `h : A* → M` when membership `w ∈ L`
depends only on `h(w)`; the statements below spell this condition out rather than naming it.
Deterministic automata are Mathlib's `DFA` (complete automata, with a transition for every state
and letter), and the size of an automaton is the number of its states.
-/
import Mathlib

namespace Transducers.Exercises

universe u

/-! ## The alphabet `{a, b}` -/

/-- The two-letter alphabet `{a, b}` of the exercises. -/
inductive AB : Type
  | a : AB
  | b : AB
  deriving DecidableEq, Fintype

lemma AB.card : Fintype.card AB = 2 := rfl

lemma AB.eq_of_iff {x y : AB} (h : x = AB.a ↔ y = AB.a) : x = y := by
  cases x <;> cases y <;> simp_all

/-! ## The monoid lower bound -/

/-- The monoid lower bound common to both exercises.  Suppose that for some words `u g`, indexed by
the `2ⁿ` functions `g : {0, …, n-1} → {a, b}`, and for every `j < n` there is a two-sided context
`p j _ q j` that turns membership in `L` into the test `g j = a`.  Then every finite monoid
recognising `L` has at least `2ⁿ` elements, since the words `u g` must have pairwise distinct
images. -/
theorem two_pow_le_card_of_contexts {A : Type} {M : Type u} [Monoid M] [Finite M]
    (h : FreeMonoid A →* M) (L : Language A)
    (hrec : ∀ w w' : List A, h (FreeMonoid.ofList w) = h (FreeMonoid.ofList w') →
      (w ∈ L ↔ w' ∈ L))
    (n : ℕ) (u : (Fin n → AB) → List A) (p q : Fin n → List A)
    (hpq : ∀ g j, p j ++ u g ++ q j ∈ L ↔ g j = AB.a) :
    2 ^ n ≤ Nat.card M := by
  let f : (Fin n → AB) → M := fun g => h (FreeMonoid.ofList (u g))
  have hf : Function.Injective f := by
    intro g g' hgg'
    funext j
    apply AB.eq_of_iff
    rw [← hpq g j, ← hpq g' j]
    apply hrec
    simp only [FreeMonoid.ofList_append, map_mul]
    exact congrArg (fun x => h (FreeMonoid.ofList (p j)) * x * h (FreeMonoid.ofList (q j))) hgg'
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card (Fin n → AB) = 2 ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, AB.card]
  omega

/-! ## Exercise `exer:monoid-vs-deterministic-automaton` -/

/-- The language `{w ∈ {a,b}* | the n-th letter of w is a}` of the solution (letters are counted
from `1`, so the `n`-th letter is `w[n-1]`). -/
def nthLetterA (n : ℕ) : Language AB := {w | w[n - 1]? = some AB.a}

/-- The deterministic automaton for `nthLetterA n`: the states `inl i` (`i < n`) count the letters
read so far, and the two states `inr true`, `inr false` remember, once the `n`-th letter has been
read, whether it was `a`. -/
def nthLetterDFA (n : ℕ) (hn : 0 < n) : DFA AB (Fin n ⊕ Bool) where
  step s x := match s with
    | Sum.inl i => if hi : i.val + 1 < n then Sum.inl ⟨i.val + 1, hi⟩ else Sum.inr (decide (x = AB.a))
    | Sum.inr c => Sum.inr c
  start := Sum.inl ⟨0, hn⟩
  accept := {Sum.inr true}

lemma nthLetterDFA_evalFrom_inr (n : ℕ) (hn : 0 < n) (c : Bool) :
    ∀ w : List AB, (nthLetterDFA n hn).evalFrom (Sum.inr c) w = Sum.inr c
  | [] => rfl
  | x :: w => by
    rw [DFA.evalFrom_cons]
    exact nthLetterDFA_evalFrom_inr n hn c w

lemma nthLetterDFA_evalFrom_inl (n : ℕ) (hn : 0 < n) :
    ∀ (w : List AB) (i : Fin n), (nthLetterDFA n hn).evalFrom (Sum.inl i) w ∈
      (nthLetterDFA n hn).accept ↔ w[n - 1 - i.val]? = some AB.a
  | [], i => by simp [nthLetterDFA]
  | x :: w, i => by
    rw [DFA.evalFrom_cons]
    by_cases hi : i.val + 1 < n
    · have hs : (nthLetterDFA n hn).step (Sum.inl i) x = Sum.inl ⟨i.val + 1, hi⟩ := by
        simp [nthLetterDFA, hi]
      rw [hs, nthLetterDFA_evalFrom_inl n hn w]
      have : n - 1 - i.val = (n - 1 - (i.val + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]
    · have hs : (nthLetterDFA n hn).step (Sum.inl i) x = Sum.inr (decide (x = AB.a)) := by
        simp [nthLetterDFA, hi]
      rw [hs, nthLetterDFA_evalFrom_inr]
      have : n - 1 - i.val = 0 := by omega
      rw [this]
      simp [nthLetterDFA]

lemma nthLetterDFA_accepts (n : ℕ) (hn : 0 < n) :
    (nthLetterDFA n hn).accepts = nthLetterA n := by
  ext w
  rw [DFA.mem_accepts, DFA.eval]
  exact nthLetterDFA_evalFrom_inl n hn w ⟨0, hn⟩

/-- **Exercise `exer:monoid-vs-deterministic-automaton`.**  The monoid recognising a language can
be exponentially bigger than a deterministic automaton.  For `n ≥ 1`, the language
`{w ∈ {a,b}* | the n-th letter of w is a}` is recognised by a deterministic automaton with `n + 2`
states, but every finite monoid recognising it -- through a homomorphism `h` such that membership
`w ∈ L` depends only on `h(w)` -- has at least `2ⁿ` elements.

(The book counts `n + 1` states; that is the count without the rejecting sink state, which a
complete deterministic automaton such as Mathlib's `DFA` needs.  The minimal complete automaton has
exactly `n + 2` states.) -/
theorem monoid_vs_deterministic_automaton (n : ℕ) (hn : 1 ≤ n) :
    (∃ (Q : Type) (_ : Fintype Q) (D : DFA AB Q),
      Fintype.card Q = n + 2 ∧ D.accepts = nthLetterA n) ∧
    ∀ (M : Type u) [Monoid M] [Finite M] (h : FreeMonoid AB →* M),
      (∀ w w' : List AB, h (FreeMonoid.ofList w) = h (FreeMonoid.ofList w') →
        (w ∈ nthLetterA n ↔ w' ∈ nthLetterA n)) →
      2 ^ n ≤ Nat.card M := by
  refine ⟨⟨Fin n ⊕ Bool, inferInstance, nthLetterDFA n hn, by simp, nthLetterDFA_accepts n hn⟩, ?_⟩
  intro M _ _ h hrec
  refine two_pow_le_card_of_contexts h _ hrec n (fun g => List.ofFn g)
    (fun j => List.replicate (n - 1 - j.val) AB.a) (fun _ => []) fun g j => ?_
  have hj := j.isLt
  show (List.replicate (n - 1 - j.val) AB.a ++ List.ofFn g ++ [])[n - 1]? = some AB.a ↔ _
  rw [List.append_nil, List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
  simp only [List.length_replicate]
  rw [show n - 1 - (n - 1 - j.val) = j.val by omega]
  simp

/-! ## Exercise `exer:monoid-vs-deterministic-automaton-strengthened` -/

/-- The language of the strengthened exercise: the words of length exactly `2n` whose `n`-th letter
is `a`. -/
def nthLetterAOfLength (n : ℕ) : Language AB := {w | w.length = 2 * n ∧ w[n - 1]? = some AB.a}

/-- A deterministic automaton accepting the words of length exactly `N` whose letter at (`0`-based)
position `p` is `a`: it counts the letters read up to `N`, remembers in a Boolean whether the letter
at position `p` was `a`, and goes to the sink `none` on a word longer than `N`. -/
def lenPosDFA (N p : ℕ) : DFA AB (Option (Fin (N + 1) × Bool)) where
  step s x := match s with
    | none => none
    | some (i, c) =>
      if hi : i.val < N then some (⟨i.val + 1, by omega⟩, if i.val = p then decide (x = AB.a) else c)
      else none
  start := some (0, false)
  accept := {some (Fin.last N, true)}

lemma lenPosDFA_evalFrom_none (N p : ℕ) :
    ∀ w : List AB, (lenPosDFA N p).evalFrom none w = none
  | [] => rfl
  | x :: w => by
    rw [DFA.evalFrom_cons]
    exact lenPosDFA_evalFrom_none N p w

lemma lenPosDFA_evalFrom_some (N p : ℕ) (hp : p < N) :
    ∀ (w : List AB) (i : Fin (N + 1)) (c : Bool),
      (lenPosDFA N p).evalFrom (some (i, c)) w ∈ (lenPosDFA N p).accept ↔
        i.val + w.length = N ∧ (if p < i.val then c = true else w[p - i.val]? = some AB.a)
  | [], i, c => by
    simp only [DFA.evalFrom_nil, lenPosDFA, Set.mem_singleton_iff, Option.some.injEq,
      Prod.mk.injEq, List.length_nil, add_zero, List.getElem?_nil, reduceCtorEq, Fin.ext_iff,
      Fin.val_last]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [if_pos (by omega)]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [if_pos (by omega)] at h2⟩
  | x :: w, i, c => by
    rw [DFA.evalFrom_cons]
    by_cases hi : i.val < N
    · have hs : (lenPosDFA N p).step (some (i, c)) x =
          some (⟨i.val + 1, by omega⟩, if i.val = p then decide (x = AB.a) else c) := by
        simp [lenPosDFA, hi]
      rw [hs, lenPosDFA_evalFrom_some N p hp w]
      simp only [List.length_cons]
      rcases lt_trichotomy p i.val with h | h | h
      · rw [if_pos (by omega), if_pos h, if_neg (by omega)]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
      · subst h
        rw [if_pos (by omega), if_pos rfl, if_neg (lt_irrefl _), Nat.sub_self]
        simp only [decide_eq_true_eq, List.getElem?_cons_zero, Option.some.injEq]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
      · rw [if_neg (by omega), if_neg (by omega)]
        rw [show p - i.val = (p - (i.val + 1)) + 1 by omega, List.getElem?_cons_succ]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
    · have hs : (lenPosDFA N p).step (some (i, c)) x = none := by
        simp [lenPosDFA, hi]
      rw [hs, lenPosDFA_evalFrom_none]
      simp only [lenPosDFA, Set.mem_singleton_iff, reduceCtorEq, false_iff, not_and,
        List.length_cons]
      intro h
      have := i.isLt
      omega

lemma lenPosDFA_accepts (N p : ℕ) (hp : p < N) (w : List AB) :
    w ∈ (lenPosDFA N p).accepts ↔ w.length = N ∧ w[p]? = some AB.a := by
  rw [DFA.mem_accepts, DFA.eval]
  have := lenPosDFA_evalFrom_some N p hp w 0 false
  simp only [Fin.val_zero, zero_add, Nat.not_lt_zero, if_false, Nat.sub_zero] at this
  exact this

/-- **Exercise `exer:monoid-vs-deterministic-automaton-strengthened`.**  A family of languages
whose recognising monoids are exponentially bigger than both deterministic left-to-right and
deterministic right-to-left automata.  For `n ≥ 1`, the language of words of length exactly `2n`
whose `n`-th letter is `a` is recognised

* by a deterministic automaton with `4n + 3` states reading from left to right, and
* by a deterministic automaton with `4n + 3` states reading from right to left (i.e. run on the
  reversed word),

but every finite monoid recognising it has at least `2ⁿ` elements.  (The book's solution only says
that the automata have size polynomial in `n`; the construction gives the explicit linear bound.) -/
theorem monoid_vs_deterministic_automaton_strengthened (n : ℕ) (hn : 1 ≤ n) :
    (∃ (Q : Type) (_ : Fintype Q) (D : DFA AB Q),
      Fintype.card Q = 4 * n + 3 ∧ D.accepts = nthLetterAOfLength n) ∧
    (∃ (Q : Type) (_ : Fintype Q) (D : DFA AB Q),
      Fintype.card Q = 4 * n + 3 ∧ ∀ w : List AB, w.reverse ∈ D.accepts ↔ w ∈ nthLetterAOfLength n) ∧
    ∀ (M : Type u) [Monoid M] [Finite M] (h : FreeMonoid AB →* M),
      (∀ w w' : List AB, h (FreeMonoid.ofList w) = h (FreeMonoid.ofList w') →
        (w ∈ nthLetterAOfLength n ↔ w' ∈ nthLetterAOfLength n)) →
      2 ^ n ≤ Nat.card M := by
  have hcard : Fintype.card (Option (Fin (2 * n + 1) × Bool)) = 4 * n + 3 := by
    simp [Fintype.card_option, Fintype.card_prod]; ring
  refine ⟨⟨_, inferInstance, lenPosDFA (2 * n) (n - 1), hcard, ?_⟩,
    ⟨_, inferInstance, lenPosDFA (2 * n) n, hcard, fun w => ?_⟩, ?_⟩
  · ext w
    rw [lenPosDFA_accepts _ _ (by omega)]
    rfl
  · rw [lenPosDFA_accepts _ _ (by omega), List.length_reverse]
    simp only [nthLetterAOfLength]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [List.getElem?_reverse (by omega), h1] at h2
      rwa [show 2 * n - 1 - n = n - 1 by omega] at h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [List.getElem?_reverse (by omega), h1, show 2 * n - 1 - n = n - 1 by omega]
      exact h2
  · intro M _ _ h hrec
    refine two_pow_le_card_of_contexts h _ hrec n (fun g => List.ofFn g)
      (fun j => List.replicate (n - 1 - j.val) AB.a)
      (fun j => List.replicate (j.val + 1) AB.a) fun g j => ?_
    have hj := j.isLt
    show (List.replicate (n - 1 - j.val) AB.a ++ List.ofFn g ++
        List.replicate (j.val + 1) AB.a).length = 2 * n ∧
      (List.replicate (n - 1 - j.val) AB.a ++ List.ofFn g ++
        List.replicate (j.val + 1) AB.a)[n - 1]? = some AB.a ↔ _
    simp only [List.length_append, List.length_replicate, List.length_ofFn]
    rw [List.append_assoc, List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
    simp only [List.length_replicate]
    rw [show n - 1 - (n - 1 - j.val) = j.val by omega,
      List.getElem?_append_left (by simp only [List.length_ofFn]; omega)]
    simp only [List.getElem?_ofFn]
    constructor
    · rintro ⟨-, h2⟩
      simpa using h2
    · intro h2
      refine ⟨by omega, ?_⟩
      simp [h2]

/-! ## Exercise `exer:idempotents-in-monoid-of-functions` -/

/-- **Exercise `exer:idempotents-in-monoid-of-functions`.**  The idempotents of the monoid of
functions `Q → Q` (under composition, Mathlib's `Function.End Q`) are exactly the functions that are
the identity on their image: `e ∘ e = e` if and only if `e q = q` for every `q` in the image of `e`.
The set `Q` is arbitrary. -/
theorem idempotent_function_iff {Q : Type u} (e : Function.End Q) :
    IsIdempotentElem e ↔ ∀ q ∈ Set.range e, e q = q := by
  constructor
  · rintro he q ⟨r, rfl⟩
    exact congrFun he r
  · intro he
    funext q
    exact he (e q) ⟨q, rfl⟩

/-! ## Exercise `exer:idempotents-in-monoid-of-relations` -/

/-- The monoid of binary relations on `Q`: the product `R * S` is the composition "first `R`, then
`S`", i.e. `(R * S) q p` iff `R q r` and `S r p` for some `r`, and the identity is equality. -/
def RelMonoid (Q : Type u) : Type u := Q → Q → Prop

instance (Q : Type u) : Monoid (RelMonoid Q) where
  mul R S := fun q p => ∃ r, R q r ∧ S r p
  one := fun q p => q = p
  mul_assoc R S T := by
    funext q p
    apply propext
    constructor
    · rintro ⟨r, ⟨s, h1, h2⟩, h3⟩
      exact ⟨s, h1, r, h2, h3⟩
    · rintro ⟨s, h1, r, h2, h3⟩
      exact ⟨r, ⟨s, h1, h2⟩, h3⟩
  one_mul R := by
    funext q p
    apply propext
    constructor
    · rintro ⟨r, rfl, h⟩
      exact h
    · intro h
      exact ⟨q, rfl, h⟩
  mul_one R := by
    funext q p
    apply propext
    constructor
    · rintro ⟨r, h, rfl⟩
      exact h
    · intro h
      exact ⟨p, h, rfl⟩

lemma RelMonoid.mul_apply {Q : Type u} (R S : RelMonoid Q) (q p : Q) :
    (R * S) q p = ∃ r, R q r ∧ S r p := rfl

/-- **Exercise `exer:idempotents-in-monoid-of-relations`** (arbitrary `Q`).  A binary relation `R`
on `Q` is an idempotent of the monoid of relations if and only if it is transitive (`R² ⊆ R`) and
every pair `(q, p) ∈ R` splits into two steps `(q, r), (r, p) ∈ R` (`R ⊆ R²`). -/
theorem idempotent_relation_iff {Q : Type u} (R : RelMonoid Q) :
    IsIdempotentElem R ↔
      (∀ q r p, R q r → R r p → R q p) ∧ (∀ q p, R q p → ∃ r, R q r ∧ R r p) := by
  constructor
  · intro hR
    have key : ∀ q p, R q p = ∃ r, R q r ∧ R r p := fun q p => by
      rw [← RelMonoid.mul_apply, hR]
    refine ⟨fun q r p h1 h2 => ?_, fun q p h => ?_⟩
    · rw [key]; exact ⟨r, h1, h2⟩
    · rw [key] at h; exact h
  · rintro ⟨htr, hsp⟩
    funext q p
    apply propext
    rw [RelMonoid.mul_apply]
    constructor
    · rintro ⟨r, h1, h2⟩
      exact htr q r p h1 h2
    · exact hsp q p

/-- Splitting a pair `k` times: a pair of a relation that splits every pair is joined by a path of
`k + 1` steps. -/
lemma rel_path_of_split {Q : Type u} (R : Q → Q → Prop) (hsp : ∀ q p, R q p → ∃ r, R q r ∧ R r p) :
    ∀ (k : ℕ) (q p : Q), R q p →
      ∃ f : ℕ → Q, f 0 = q ∧ f (k + 1) = p ∧ ∀ i ≤ k, R (f i) (f (i + 1))
  | 0, q, p, h => ⟨fun i => if i = 0 then q else p, by simp, by simp, fun i hi => by
      obtain rfl : i = 0 := by omega
      simpa using h⟩
  | k + 1, q, p, h => by
    obtain ⟨f, hf0, hfk, hf⟩ := rel_path_of_split R hsp k q p h
    obtain ⟨r, hr1, hr2⟩ := hsp (f k) p (hfk ▸ hf k le_rfl)
    refine ⟨fun i => if i ≤ k then f i else if i = k + 1 then r else p, by simp [hf0],
      by simp, fun i hi => ?_⟩
    rcases Nat.lt_or_ge i k with h1 | h1
    · simp only [if_pos h1.le, if_pos (show i + 1 ≤ k by omega)]
      exact hf i h1.le
    · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
      · have hik : i = k := by omega
        rw [hik]
        simp only [le_refl, if_true, if_neg (show ¬ k + 1 ≤ k by omega)]
        exact hr1
      · obtain rfl : i = k + 1 := by omega
        simp only [if_neg (show ¬ k + 1 ≤ k by omega), if_true,
          if_neg (show ¬ k + 1 + 1 ≤ k by omega), if_neg (show ¬ k + 1 + 1 = k + 1 by omega)]
        exact hr2

/-- **Exercise `exer:idempotents-in-monoid-of-relations`** (finite `Q`).  If `Q` is finite, the
splitting condition can be strengthened to splitting through a loop: `R` is an idempotent if and
only if it is transitive and every pair `(q, p) ∈ R` splits as `(q, r), (r, r), (r, p) ∈ R` for some
`r`.  (Splitting `|Q| + 1` times yields a path on which some state is visited twice; by
transitivity, that state carries a loop.) -/
theorem idempotent_relation_iff_of_finite {Q : Type u} [Finite Q] (R : RelMonoid Q) :
    IsIdempotentElem R ↔
      (∀ q r p, R q r → R r p → R q p) ∧ (∀ q p, R q p → ∃ r, R q r ∧ R r r ∧ R r p) := by
  rw [idempotent_relation_iff]
  constructor
  · rintro ⟨htr, hsp⟩
    refine ⟨htr, fun q p h => ?_⟩
    haveI : Fintype Q := Fintype.ofFinite Q
    set k := Fintype.card Q + 1 with hk
    obtain ⟨f, hf0, hfk, hf⟩ := rel_path_of_split R hsp k q p h
    have hlong : ∀ j i, i < j → j ≤ k + 1 → R (f i) (f j) := by
      intro j
      induction j with
      | zero => intro i hi; omega
      | succ j ih =>
        intro i hi hj
        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with h1 | h1
        · subst h1; exact hf i (by omega)
        · exact htr _ _ _ (ih i h1 (by omega)) (hf j (by omega))
    obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card Q + 1) => f (i.val + 1)) (by simp)
    have key : ∀ i j : Fin (Fintype.card Q + 1), i.val < j.val → f (i.val + 1) = f (j.val + 1) →
        ∃ r, R q r ∧ R r r ∧ R r p := by
      intro i j hlt heq
      have hi := i.isLt
      have hj := j.isLt
      refine ⟨f (i.val + 1), ?_, ?_, ?_⟩
      · rw [← hf0]; exact hlong _ _ (by omega) (by omega)
      · conv_rhs => rw [heq]
        exact hlong _ _ (by omega) (by omega)
      · rw [← hfk, heq]; exact hlong _ _ (by omega) le_rfl
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · exact key i j hlt hfij
    · exact key j i hlt hfij.symm
  · rintro ⟨htr, hsp⟩
    refine ⟨htr, fun q p h => ?_⟩
    obtain ⟨r, h1, -, h3⟩ := hsp q p h
    exact ⟨r, h1, h3⟩

end Transducers.Exercises
