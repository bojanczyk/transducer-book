/-
The exercise of the chapter on rational functions (`rational-functions.tex`) of
*Transducers* (M. Bojańczyk) on deciding unambiguity of an nfa.
-/
import RequestProject.Common

/-!
# Unambiguity of an nfa is decidable

Exercise `exer:decide-unambiguous`: one can decide whether a given nfa that recognises a
language (not a function or a relation) is unambiguous, that is, whether every accepted input
has exactly one accepting run.

The automaton is Mathlib's `NFA A Q`, whose transitions read exactly one letter; this is the
ε-free form that the solution reduces to in its first sentence ("we can assume that the
automaton has no transitions with empty input").  A *run* on an input `w` from a state `q` is
the list `qs` of the states visited after each letter of `w` (`RunFrom`), so the run itself is
`q :: qs`; `mem_accepts_iff_exists_accRun` checks against Mathlib's semantics that the language
of the automaton is the set of inputs with an accepting run.  Two runs on the same input use
different transitions somewhere exactly when the two lists differ, since a transition is
determined by its source, its letter and its target, so ambiguity is stated as the existence of
two distinct accepting runs (`Ambiguous`).

The formalisation follows the solution in two steps, as the two other decidability exercises of
the book are formalised: first the criterion, `ambiguous_iff_reach` — the automaton is ambiguous
exactly when the product automaton of the solution, which runs two copies of the automaton on
the same input and carries a bit recording whether the two copies have already parted, reaches a
pair of accepting states with the bit set — and then the resulting decision procedure,
`decidableUnambiguousNFA`.  The section `FinReach` provides what the last step of the solution
takes for granted, that reachability in a finite graph is decidable; it is decided here by
saturation, and not, as the solution's "polynomial time" suggests, by a graph search, since the
project has no model of running time.
-/

namespace Transducers.Exercises

/-! ### Reachability in a finite graph -/

namespace FinReach

variable {S : Type*} [Fintype S] [DecidableEq S] (r : S → S → Prop) [DecidableRel r]

/-- One round of saturation: add to `X` every state reachable from `X` in one step. -/
def sat (X : Finset S) : Finset S := X ∪ X.biUnion (fun x => Finset.univ.filter (r x))

lemma mem_sat {X : Finset S} {y : S} : y ∈ sat r X ↔ y ∈ X ∨ ∃ x ∈ X, r x y := by
  simp [sat]

lemma subset_sat (X : Finset S) : X ⊆ sat r X := Finset.subset_union_left

lemma sat_mono {X Y : Finset S} (h : X ⊆ Y) : sat r X ⊆ sat r Y := by
  intro y hy
  rw [mem_sat] at hy ⊢
  rcases hy with hy | ⟨x, hx, hxy⟩
  · exact Or.inl (h hy)
  · exact Or.inr ⟨x, h hx, hxy⟩

lemma iter_mono (X : Finset S) (n : ℕ) : (sat r)^[n] X ⊆ (sat r)^[n + 1] X := by
  induction n with
  | zero => simpa using subset_sat r X
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' (n := n + 1)]
      exact sat_mono r ih

lemma iter_mono_le (X : Finset S) {m n : ℕ} (h : m ≤ n) : (sat r)^[m] X ⊆ (sat r)^[n] X := by
  induction n with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h' | h'
      · exact (ih (by omega)).trans (iter_mono r X n)
      · have : m = n + 1 := by omega
        subst this; exact subset_rfl

lemma iter_stab (X : Finset S) {n : ℕ} (h : (sat r)^[n] X = (sat r)^[n + 1] X) :
    ∀ m, n ≤ m → (sat r)^[m] X = (sat r)^[n] X := by
  intro m hm
  induction m with
  | zero => simp_all
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h' | h'
      · have hmn : n ≤ m := by omega
        rw [Function.iterate_succ_apply', ih hmn,
          show sat r ((sat r)^[n] X) = (sat r)^[n + 1] X from
            (Function.iterate_succ_apply' (sat r) n X).symm]
        exact h.symm
      · have : n = m + 1 := by omega
        subst this; rfl

lemma card_iter_ge (X : Finset S) (n : ℕ) :
    (∃ k < n, (sat r)^[k] X = (sat r)^[k + 1] X) ∨ n ≤ ((sat r)^[n] X).card := by
  induction n with
  | zero => exact Or.inr (by simp)
  | succ n ih =>
      rcases ih with ⟨k, hk, hk2⟩ | hc
      · exact Or.inl ⟨k, by omega, hk2⟩
      · by_cases hstab : (sat r)^[n] X = (sat r)^[n + 1] X
        · exact Or.inl ⟨n, by omega, hstab⟩
        · refine Or.inr ?_
          have hss : (sat r)^[n] X ⊂ (sat r)^[n + 1] X :=
            ⟨iter_mono r X n, fun hcon => hstab (Finset.Subset.antisymm (iter_mono r X n) hcon)⟩
          have := Finset.card_lt_card hss
          omega

lemma iter_subset_card (X : Finset S) (m : ℕ) :
    (sat r)^[m] X ⊆ (sat r)^[Fintype.card S] X := by
  rcases card_iter_ge r X (Fintype.card S + 1) with ⟨k, hk, hk2⟩ | hc
  · have hkle : k ≤ Fintype.card S := by omega
    have hcard : (sat r)^[Fintype.card S] X = (sat r)^[k] X := iter_stab r X hk2 _ hkle
    rcases Nat.lt_or_ge m k with h | h
    · rw [hcard]; exact iter_mono_le r X (le_of_lt h)
    · rw [iter_stab r X hk2 m h, hcard]
  · have hle := Finset.card_le_univ ((sat r)^[Fintype.card S + 1] X)
    omega

/-- The set of states reachable from `X`, computed by saturating `Fintype.card S` times. -/
def reach (X : Finset S) : Finset S := (sat r)^[Fintype.card S] X

lemma mem_iter_imp {X : Finset S} :
    ∀ (n : ℕ) (y : S), y ∈ (sat r)^[n] X → ∃ x ∈ X, Relation.ReflTransGen r x y := by
  intro n
  induction n with
  | zero => intro y hy; exact ⟨y, hy, Relation.ReflTransGen.refl⟩
  | succ n ih =>
      intro y hy
      rw [Function.iterate_succ_apply', mem_sat] at hy
      rcases hy with hy | ⟨z, hz, hzy⟩
      · exact ih y hy
      · obtain ⟨x, hx, hxz⟩ := ih z hz
        exact ⟨x, hx, hxz.tail hzy⟩

lemma exists_mem_iter {X : Finset S} {x y : S} (hx : x ∈ X) (h : Relation.ReflTransGen r x y) :
    ∃ n, y ∈ (sat r)^[n] X := by
  induction h with
  | refl => exact ⟨0, hx⟩
  | tail _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by rw [Function.iterate_succ_apply', mem_sat]; exact Or.inr ⟨_, hn, hstep⟩⟩

/-- `reach` computes reachability. -/
theorem mem_reach {X : Finset S} {y : S} :
    y ∈ reach r X ↔ ∃ x ∈ X, Relation.ReflTransGen r x y := by
  constructor
  · exact mem_iter_imp r _ y
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨n, hn⟩ := exists_mem_iter r hx hxy
    exact iter_subset_card r X n hn

/-- Reachability in a finite graph with a decidable edge relation is decidable. -/
instance decidableReflTransGen : DecidableRel (Relation.ReflTransGen r) := fun x y =>
  decidable_of_iff (y ∈ reach r {x}) (by simp [mem_reach])

end FinReach

/-! ### Runs of an nfa -/

variable {A Q : Type}

/-- `RunFrom M q w qs` says that `qs` is the list of states that a run of `M` on the input
`w`, started in the state `q`, visits after reading each successive letter; so `qs` has the
length of `w` and the run itself is the list `q :: qs`. -/
inductive RunFrom (M : NFA A Q) : Q → List A → List Q → Prop
  | nil (q : Q) : RunFrom M q [] []
  | cons {q a r w qs} : r ∈ M.step q a → RunFrom M r w qs → RunFrom M q (a :: w) (r :: qs)

lemma RunFrom.length {M : NFA A Q} {q : Q} {w : List A} {qs : List Q} (h : RunFrom M q w qs) :
    qs.length = w.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

lemma getLastD_cons (q r : Q) (qs : List Q) : (r :: qs).getLastD q = qs.getLastD r := by
  cases qs with
  | nil => simp
  | cons b bs => simp [List.getLastD]

lemma RunFrom.snoc {M : NFA A Q} {q : Q} {w : List A} {qs : List Q} {a : A} {r : Q}
    (h : RunFrom M q w qs) (hstep : r ∈ M.step (qs.getLastD q) a) :
    RunFrom M q (w ++ [a]) (qs ++ [r]) := by
  induction h with
  | nil q => simpa using RunFrom.cons (by simpa using hstep) (RunFrom.nil r)
  | @cons q a' r' w qs hst hrun ih =>
      rw [getLastD_cons] at hstep
      simpa using RunFrom.cons hst (ih hstep)

lemma mem_evalFrom_singleton_iff (M : NFA A Q) (q : Q) (w : List A) (p : Q) :
    p ∈ M.evalFrom {q} w ↔ ∃ qs, RunFrom M q w qs ∧ qs.getLastD q = p := by
  induction w generalizing q with
  | nil =>
      constructor
      · intro h
        simp [NFA.evalFrom] at h
        exact ⟨[], RunFrom.nil q, by simp [h]⟩
      · rintro ⟨qs, hr, hl⟩
        cases hr
        simp [NFA.evalFrom] at hl ⊢
        exact hl.symm
  | cons a w ih =>
      rw [NFA.evalFrom_cons, NFA.stepSet_singleton, NFA.mem_evalFrom_iff_exists]
      constructor
      · rintro ⟨r, hr, hp⟩
        obtain ⟨qs, hrun, hlast⟩ := (ih r).1 hp
        exact ⟨r :: qs, RunFrom.cons hr hrun, by rw [getLastD_cons]; exact hlast⟩
      · rintro ⟨qs, hrun, hlast⟩
        cases hrun with
        | cons hstep hrest =>
            rename_i r qs'
            rw [getLastD_cons] at hlast
            exact ⟨r, hstep, (ih r).2 ⟨qs', hrest, hlast⟩⟩

/-- An accepting run of `M` on the input `w`: it starts in the initial state `q`, visits the
states `qs`, and its last state is accepting. -/
def AccRun (M : NFA A Q) (w : List A) (q : Q) (qs : List Q) : Prop :=
  q ∈ M.start ∧ RunFrom M q w qs ∧ qs.getLastD q ∈ M.accept

/-- The language of an nfa is the set of inputs that admit an accepting run. -/
theorem mem_accepts_iff_exists_accRun (M : NFA A Q) (w : List A) :
    w ∈ M.accepts ↔ ∃ q qs, AccRun M w q qs := by
  rw [NFA.mem_accepts]
  constructor
  · rintro ⟨p, hp, hev⟩
    rw [NFA.mem_evalFrom_iff_exists] at hev
    obtain ⟨q, hq, hqev⟩ := hev
    obtain ⟨qs, hrun, hlast⟩ := (mem_evalFrom_singleton_iff M q w p).1 hqev
    exact ⟨q, qs, hq, hrun, by rw [hlast]; exact hp⟩
  · rintro ⟨q, qs, hq, hrun, hacc⟩
    refine ⟨qs.getLastD q, hacc, ?_⟩
    rw [NFA.mem_evalFrom_iff_exists]
    exact ⟨q, hq, (mem_evalFrom_singleton_iff M q w _).2 ⟨qs, hrun, rfl⟩⟩

/-- An nfa is *ambiguous* if some input admits two distinct accepting runs. -/
def Ambiguous (M : NFA A Q) : Prop :=
  ∃ (w : List A) (q : Q) (qs : List Q) (q' : Q) (qs' : List Q),
    AccRun M w q qs ∧ AccRun M w q' qs' ∧ (q, qs) ≠ (q', qs')

/-- An nfa is *unambiguous* if every input admits at most one accepting run. -/
def UnambiguousNFA (M : NFA A Q) : Prop :=
  ∀ (w : List A) (q : Q) (qs : List Q) (q' : Q) (qs' : List Q),
    AccRun M w q qs → AccRun M w q' qs' → q = q' ∧ qs = qs'

lemma unambiguousNFA_iff_not_ambiguous (M : NFA A Q) :
    UnambiguousNFA M ↔ ¬ Ambiguous M := by
  constructor
  · rintro h ⟨w, q, qs, q', qs', h1, h2, hne⟩
    obtain ⟨rfl, rfl⟩ := h w q qs q' qs' h1 h2
    exact hne rfl
  · intro h w q qs q' qs' h1 h2
    by_contra hcon
    exact h ⟨w, q, qs, q', qs', h1, h2, by
      intro hpair
      exact hcon ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩⟩

/-! ### The product automaton of the solution -/

variable [DecidableEq Q]

/-- The transition relation of the product automaton of the solution: two copies of `M` read
the same letter, and the bit records whether the two copies have already parted. -/
def prodStep (M : NFA A Q) : Q × Q × Bool → Q × Q × Bool → Prop :=
  fun s t => ∃ a : A, t.1 ∈ M.step s.1 a ∧ t.2.1 ∈ M.step s.2.1 a ∧
    t.2.2 = (s.2.2 || decide (t.1 ≠ t.2.1))

lemma runs_reach {M : NFA A Q} {q q' : Q} {w : List A} {qs qs' : List Q}
    (h : RunFrom M q w qs) : ∀ (_ : RunFrom M q' w qs') (b : Bool),
    Relation.ReflTransGen (prodStep M) (q, q', b)
      (qs.getLastD q, qs'.getLastD q', b || decide (qs ≠ qs')) := by
  induction h generalizing q' qs' with
  | nil q =>
      intro h' b
      cases h'
      simpa using Relation.ReflTransGen.refl
  | @cons q a r w qs hst hrun ih =>
      intro h' b
      cases h' with
      | cons hst' hrun' =>
        rename_i r' qs''
        refine Relation.ReflTransGen.head (b := (r, r', b || decide (r ≠ r'))) ⟨a, hst, hst', rfl⟩ ?_
        have hIH := ih hrun' (b || decide (r ≠ r'))
        rw [getLastD_cons, getLastD_cons]
        refine hIH.trans ?_
        have : (b || decide (r ≠ r') || decide (qs ≠ qs'')) =
            (b || decide (r :: qs ≠ r' :: qs'')) := by
          by_cases h1 : r = r' <;> by_cases h2 : qs = qs'' <;> simp [h1, h2]
        rw [this]

lemma reach_runs {M : NFA A Q} {s t : Q × Q × Bool}
    (h : Relation.ReflTransGen (prodStep M) s t) :
    ∃ (w : List A) (qs qs' : List Q), RunFrom M s.1 w qs ∧ RunFrom M s.2.1 w qs' ∧
      qs.getLastD s.1 = t.1 ∧ qs'.getLastD s.2.1 = t.2.1 ∧
      t.2.2 = (s.2.2 || decide (qs ≠ qs')) := by
  induction h with
  | refl => exact ⟨[], [], [], RunFrom.nil _, RunFrom.nil _, rfl, rfl, by simp⟩
  | @tail u t _ hstep ih =>
      obtain ⟨w, qs, qs', hr, hr', hl, hl', hb⟩ := ih
      obtain ⟨a, ha1, ha2, hb2⟩ := hstep
      refine ⟨w ++ [a], qs ++ [t.1], qs' ++ [t.2.1], hr.snoc (by rw [hl]; exact ha1),
        hr'.snoc (by rw [hl']; exact ha2), by simp, by simp, ?_⟩
      rw [hb2, hb]
      by_cases h1 : qs = qs' <;> by_cases h2 : t.1 = t.2.1 <;> simp [h1, h2]

/-- **Exercise `exer:decide-unambiguous`**, the criterion of the solution: an nfa is
ambiguous exactly when the product automaton, which runs two copies of `M` on the same input
and carries a bit recording whether the two copies have already used different transitions,
can reach a pair of accepting states with the bit set. -/
theorem ambiguous_iff_reach (M : NFA A Q) :
    Ambiguous M ↔ ∃ q ∈ M.start, ∃ q' ∈ M.start, ∃ p p' : Q, p ∈ M.accept ∧ p' ∈ M.accept ∧
      Relation.ReflTransGen (prodStep M) (q, q', decide (q ≠ q')) (p, p', true) := by
  constructor
  · rintro ⟨w, q, qs, q', qs', ⟨hq, hrun, hacc⟩, ⟨hq', hrun', hacc'⟩, hne⟩
    refine ⟨q, hq, q', hq', qs.getLastD q, qs'.getLastD q', hacc, hacc', ?_⟩
    have := runs_reach hrun hrun' (decide (q ≠ q'))
    have hbit : (decide (q ≠ q') || decide (qs ≠ qs')) = true := by
      by_cases h1 : q = q'
      · subst h1
        have : qs ≠ qs' := fun h => hne (by rw [h])
        simp [this]
      · simp [h1]
    rwa [hbit] at this
  · rintro ⟨q, hq, q', hq', p, p', hp, hp', hreach⟩
    obtain ⟨w, qs, qs', hrun, hrun', hl, hl', hb⟩ := reach_runs hreach
    refine ⟨w, q, qs, q', qs', ⟨hq, hrun, by rw [hl]; exact hp⟩, ⟨hq', hrun', by
      rw [hl']; exact hp'⟩, ?_⟩
    intro hpair
    have h1 : q = q' := congrArg Prod.fst hpair
    have h2 : qs = qs' := congrArg Prod.snd hpair
    rw [h1, h2] at hb
    simp at hb

/-! ### Decidability -/

section Decide

variable [Fintype Q] [Fintype A] (M : NFA A Q)
  [∀ q a p, Decidable (p ∈ M.step q a)] [DecidablePred (· ∈ M.start)]
  [DecidablePred (· ∈ M.accept)]

instance decidableProdStep : DecidableRel (prodStep M) := fun _ _ => by
  unfold prodStep; infer_instance

/-- **Exercise `exer:decide-unambiguous`**: unambiguity of an nfa is decidable. -/
instance decidableAmbiguous : Decidable (Ambiguous M) :=
  decidable_of_iff _ (ambiguous_iff_reach M).symm

/-- **Exercise `exer:decide-unambiguous`**: unambiguity of an nfa is decidable. -/
instance decidableUnambiguousNFA : Decidable (UnambiguousNFA M) :=
  decidable_of_iff _ (unambiguousNFA_iff_not_ambiguous M).symm

end Decide

/-! ### The decision procedure at work

A check that the procedure really runs, and that the notions above are not vacuous: the
automaton with two initial states, both accepting, that loops in each of them is ambiguous, and
`decide` says so. -/

/-- The automaton with two states, both initial and both accepting, all of whose transitions
are available. -/
def exTwoStart : NFA (Fin 1) (Fin 2) := ⟨fun _ _ => Set.univ, Set.univ, Set.univ⟩

instance : ∀ q a p, Decidable (p ∈ exTwoStart.step q a) := fun _ _ _ => by
  unfold exTwoStart; simp; infer_instance

instance : DecidablePred (· ∈ exTwoStart.start) := fun _ => by
  unfold exTwoStart; simp; infer_instance

instance : DecidablePred (· ∈ exTwoStart.accept) := fun _ => by
  unfold exTwoStart; simp; infer_instance

example : Ambiguous exTwoStart := by decide

example : ¬ UnambiguousNFA exTwoStart := by decide

end Transducers.Exercises
