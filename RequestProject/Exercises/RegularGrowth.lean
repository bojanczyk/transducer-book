/-
The loop analysis of a deterministic automaton, and the growth gap theorem for regular languages.

This file supplies the analysis that the solutions of the exercises on the ideals of rational
functions (`RequestProject/Exercises/Ideals.lean`) rest on, and that the author of *Transducers*
(M. Bojańczyk) carries out only in outline.  It is the same analysis as the one behind Exercise
`exer:polynomial-image-growth-decidable`, which is formalised for Mealy machines in
`RequestProject/Exercises/PartA.lean`; here it is carried out for an arbitrary deterministic
automaton, and the polynomial case is analysed further, down to the exact degree of the growth.
-/
import RequestProject.Exercises.PartA

/-!
# The growth of a regular language

For a language `L` let `langCount L n` be the number of words of `L` of length at most `n`.  The
main result of this file, `Transducers.Exercises.regular_growth_dichotomy`, is the *growth gap
theorem*: for a nonempty regular language `L` over a finite alphabet, either

* some deterministic automaton for `L` has two loops of the same length and with different labels
  on a state that is both reachable and co-reachable — and then `L` contains all the words
  `p x^{b₁} y^{1-b₁} ⋯ s` obtained by following a sequence of bits, so that `langCount L` grows at
  least like `2^{n/|x|}` and is super-polynomial; or
* `langCount L n = Θ(n^k)` for some `k`.

The analysis is carried out on a deterministic automaton `M`.

* `Transducers.Exercises.RegGrowth.Reaches`, `Useful`, `Loopy` are the reachability, the
  co-reachability and the "lies on a nonempty loop" predicates.
* `Transducers.Exercises.RegGrowth.AmbCycle M` is condition (*) of Exercise
  `exer:polynomial-image-growth-decidable`, transported to a deterministic automaton: two loops of
  the same length and with different labels on a reachable and co-reachable state.
* `Transducers.Exercises.RegGrowth.Chain M q k` says that from `q` one can reach `k` loops, each
  one in a strictly lower strongly connected component than the previous one, and then an accepting
  state.  It is the *degree* of the growth: `Transducers.Exercises.RegGrowth.chain_lower_bound`
  turns a chain of `k` loops into `Ω(n^k)` words, and
  `Transducers.Exercises.RegGrowth.accCount_le_of_not_chain` bounds the number of words by
  `O(n^k)` when there is no chain of `k+1` loops and no ambiguous cycle.

The engine of the lower bound is `Transducers.Exercises.RegGrowth.reaches_of_loop_shift`: if the
word `u v` is also read as `x^d u v'`, where `x` is a loop at `r` and `u` leads from `r` to `r'`,
then `r` is reachable from `r'`.  It is what makes the words produced by a chain of loops pairwise
distinct.
-/

namespace Transducers.Exercises

open scoped Classical

/-- The number of words of the language `L` of length at most `n`. -/
noncomputable def langCount {A : Type} (L : Language A) (n : ℕ) : ℕ :=
  {w : List A | w ∈ L ∧ w.length ≤ n}.ncard

namespace RegGrowth

/-! ## Powers of a word -/

/-- The `d`-th power of a word. -/
def loopPow {A : Type} (x : List A) : ℕ → List A
  | 0 => []
  | d + 1 => x ++ loopPow x d

@[simp] lemma loopPow_zero {A : Type} (x : List A) : loopPow x 0 = [] := rfl

lemma loopPow_succ {A : Type} (x : List A) (d : ℕ) : loopPow x (d + 1) = x ++ loopPow x d := rfl

lemma loopPow_length {A : Type} (x : List A) (d : ℕ) :
    (loopPow x d).length = d * x.length := by
  induction d with
  | zero => simp
  | succ d ih => rw [loopPow_succ, List.length_append, ih]; ring

lemma loopPow_add {A : Type} (x : List A) (d e : ℕ) :
    loopPow x (d + e) = loopPow x d ++ loopPow x e := by
  induction d with
  | zero => simp
  | succ d ih =>
      have : d + 1 + e = (d + e) + 1 := by omega
      rw [this, loopPow_succ, loopPow_succ, ih, List.append_assoc]

/-! ## Words of bounded length -/

/-- The words of length at most `n` over a finite alphabet, as a finite set. -/
noncomputable def wordsLE (A : Type) [Fintype A] : ℕ → Finset (List A)
  | 0 => {[]}
  | n + 1 => insert [] (Finset.univ.biUnion fun a : A => (wordsLE A n).image (a :: ·))

@[simp] lemma mem_wordsLE {A : Type} [Fintype A] {n : ℕ} {w : List A} :
    w ∈ wordsLE A n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [wordsLE, List.length_eq_zero_iff]
  | succ n ih =>
      simp only [wordsLE, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · rintro (rfl | ⟨a, z, hz, rfl⟩)
        · simp
        · have := ih.mp hz
          simp only [List.length_cons]
          omega
      · intro h
        cases w with
        | nil => exact Or.inl rfl
        | cons a z =>
            refine Or.inr ⟨a, z, ih.mpr ?_, rfl⟩
            simpa using h

/-! ## Reachability in a deterministic automaton -/

section Aut

variable {A σ : Type} (M : DFA A σ)

/-- `r` is reachable from `q`. -/
def Reaches (q r : σ) : Prop := ∃ w : List A, M.evalFrom q w = r

/-- Some word takes `q` to an accepting state. -/
def Useful (q : σ) : Prop := ∃ w : List A, M.evalFrom q w ∈ M.accept

/-- `q` lies on a nonempty loop. -/
def Loopy (q : σ) : Prop := ∃ x : List A, x ≠ [] ∧ M.evalFrom q x = q

variable {M}

lemma reaches_refl (q : σ) : Reaches M q q := ⟨[], rfl⟩

lemma reaches_trans {q r p : σ} (h : Reaches M q r) (h' : Reaches M r p) : Reaches M q p := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨w ++ v, (M.evalFrom_of_append _ _ _).symm ▸ rfl⟩

lemma reaches_step (q : σ) (a : A) : Reaches M q (M.step q a) := ⟨[a], rfl⟩

lemma useful_of_reaches {q r : σ} (h : Reaches M q r) (hr : Useful M r) : Useful M q := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨v, hv⟩ := hr
  exact ⟨w ++ v, by rwa [M.evalFrom_of_append]⟩

/-! ## Chains of loops -/

/-- `Chain M q k` says that from `q` one can reach a loop, then leave its strongly connected
component and reach another loop, and so on `k` times, and finally reach an accepting state. -/
def Chain (M : DFA A σ) : σ → ℕ → Prop
  | q, 0 => Useful M q
  | q, (k + 1) => ∃ r, Reaches M q r ∧ Loopy M r ∧
      ((k = 0 ∧ Useful M r) ∨ ∃ r', Reaches M r r' ∧ ¬ Reaches M r' r ∧ Chain M r' k)

lemma chain_zero_iff {q : σ} : Chain M q 0 ↔ Useful M q := Iff.rfl

lemma chain_succ_iff {q : σ} {k : ℕ} :
    Chain M q (k + 1) ↔ ∃ r, Reaches M q r ∧ Loopy M r ∧
      ((k = 0 ∧ Useful M r) ∨ ∃ r', Reaches M r r' ∧ ¬ Reaches M r' r ∧ Chain M r' k) := Iff.rfl

lemma chain_of_reaches {q p : σ} {k : ℕ} (h : Reaches M q p) (hc : Chain M p k) :
    Chain M q k := by
  cases k with
  | zero => exact useful_of_reaches h hc
  | succ k =>
      obtain ⟨r, hr, hl, hrest⟩ := hc
      exact ⟨r, reaches_trans h hr, hl, hrest⟩

/-! ## Ambiguous cycles -/

/-- Condition (*) of Exercise `exer:polynomial-image-growth-decidable` for a deterministic
automaton: there are two loops of the same length and with different labels on a state that is
both reachable from the initial state and co-reachable to an accepting state. -/
def AmbCycle (M : DFA A σ) : Prop :=
  ∃ q : σ, Reaches M M.start q ∧ Useful M q ∧
    ∃ x y : List A, x.length = y.length ∧ x ≠ y ∧ M.evalFrom q x = q ∧ M.evalFrom q y = q

/-- If a reachable and co-reachable state carries two loops with different labels, then it
carries two loops of the same length with different labels. -/
lemma ambCycle_of_two_loops {q : σ} (hq : Reaches M M.start q) (hu : Useful M q)
    {x y : List A} (hx : M.evalFrom q x = q) (hy : M.evalFrom q y = q)
    (hne : x ≠ []) (hne' : y ≠ []) (hxy : x.head? ≠ y.head?) : AmbCycle M := by
  refine ⟨q, hq, hu, x ++ y, y ++ x, by simp [Nat.add_comm], ?_, ?_, ?_⟩
  · intro h
    apply hxy
    have h1 : (x ++ y).head? = x.head? := by
      cases x with
      | nil => exact absurd rfl hne
      | cons a t => simp
    have h2 : (y ++ x).head? = y.head? := by
      cases y with
      | nil => exact absurd rfl hne'
      | cons a t => simp
    rw [← h1, ← h2, h]
  · rw [M.evalFrom_of_append, hx, hy]
  · rw [M.evalFrom_of_append, hy, hx]

/-! ## The shifting lemma

If a word can be read in two ways along a loop, the loop can be re-entered from the state
that the word leads to.  This is what makes the words produced by a chain of loops pairwise
distinct. -/

lemma evalFrom_loopPow {r : σ} {x : List A} (hx : M.evalFrom r x = r) (d : ℕ) :
    M.evalFrom r (loopPow x d) = r := by
  induction d with
  | zero => rfl
  | succ d ihd => rw [loopPow_succ, M.evalFrom_of_append, hx, ihd]

lemma reaches_of_loop_shift {r r' : σ} {x : List A} (hx : M.evalFrom r x = r) (hxne : x ≠ []) :
    ∀ (u : List A), M.evalFrom r u = r' → ∀ (d : ℕ), 0 < d → ∀ (v v' : List A),
      u ++ v = loopPow x d ++ u ++ v' → Reaches M r' r := by
  intro u
  induction hn : u.length using Nat.strong_induction_on generalizing u with
  | _ n ih =>
  subst hn
  intro hu d hd v v' heq
  have hxpos : 0 < x.length := List.length_pos_iff.mpr hxne
  have hdlen : 0 < (loopPow x d).length := by
    rw [loopPow_length]
    exact Nat.mul_pos hd hxpos
  have hxd : M.evalFrom r (loopPow x d) = r := evalFrom_loopPow hx d
  by_cases hcase : u.length ≤ (loopPow x d).length
  · -- `u` is a prefix of `x^d`
    have hpre : u <+: loopPow x d := by
      have h1 : u <+: u ++ v := ⟨v, rfl⟩
      have h2 : loopPow x d <+: u ++ v := by
        rw [heq]
        exact ⟨u ++ v', by simp⟩
      exact (List.prefix_of_prefix_length_le h1 h2 hcase)
    obtain ⟨y, hy⟩ := hpre
    refine ⟨y, ?_⟩
    rw [← hu, ← M.evalFrom_of_append, hy, hxd]
  · -- `x^d` is a prefix of `u`
    push_neg at hcase
    have hpre : loopPow x d <+: u := by
      have h1 : u <+: u ++ v := ⟨v, rfl⟩
      have h2 : loopPow x d <+: u ++ v := by
        rw [heq]
        exact ⟨u ++ v', by simp⟩
      exact List.prefix_of_prefix_length_le h2 h1 (le_of_lt hcase)
    obtain ⟨u₂, hu₂⟩ := hpre
    have hlen₂ : u₂.length < u.length := by
      have := congrArg List.length hu₂
      simp only [List.length_append] at this
      omega
    have hu₂eval : M.evalFrom r u₂ = r' := by
      rw [← hu, ← hu₂, M.evalFrom_of_append, hxd]
    have heq₂ : u₂ ++ v = loopPow x d ++ u₂ ++ v' := by
      have : loopPow x d ++ (u₂ ++ v) = loopPow x d ++ (loopPow x d ++ u₂ ++ v') := by
        calc loopPow x d ++ (u₂ ++ v) = (loopPow x d ++ u₂) ++ v := by simp
          _ = u ++ v := by rw [hu₂]
          _ = loopPow x d ++ u ++ v' := heq
          _ = loopPow x d ++ (loopPow x d ++ u₂ ++ v') := by rw [hu₂]; simp
      exact List.append_cancel_left this
    exact ih u₂.length hlen₂ u₂ rfl hu₂eval d hd v v' heq₂

/-! ## Counting the states and the accepted words -/

variable [Fintype σ]

/-- The states reachable from `q`. -/
noncomputable def reachFin (M : DFA A σ) (q : σ) : Finset σ :=
  Finset.univ.filter (fun r => Reaches M q r)

@[simp] lemma mem_reachFin {q r : σ} : r ∈ reachFin M q ↔ Reaches M q r := by
  simp [reachFin]

lemma reachFin_subset {q r : σ} (h : Reaches M q r) : reachFin M r ⊆ reachFin M q := by
  intro p hp
  rw [mem_reachFin] at hp ⊢
  exact reaches_trans h hp

lemma reachFin_card_lt {q r : σ} (h : Reaches M q r) (h' : ¬ Reaches M r q) :
    (reachFin M r).card < (reachFin M q).card := by
  refine Finset.card_lt_card ⟨reachFin_subset h, fun hsub => ?_⟩
  have : q ∈ reachFin M r := hsub (mem_reachFin.mpr (reaches_refl q))
  exact h' (mem_reachFin.mp this)

/-- A chain of loops from `q` uses at most as many loops as there are states reachable
from `q`. -/
lemma chain_card_le {q : σ} {k : ℕ} (h : Chain M q k) : k ≤ (reachFin M q).card := by
  induction k generalizing q with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      obtain ⟨r, hqr, -, hrest⟩ := h
      rcases hrest with ⟨rfl, -⟩ | ⟨r', hrr', hnot, hc⟩
      · have : q ∈ reachFin M q := mem_reachFin.mpr (reaches_refl q)
        have := Finset.card_pos.mpr ⟨q, this⟩
        omega
      · have hqr' : Reaches M q r' := reaches_trans hqr hrr'
        have hnotq : ¬ Reaches M r' r := hnot
        have hlt : (reachFin M r').card < (reachFin M r).card := reachFin_card_lt hrr' hnotq
        have hsub : (reachFin M r).card ≤ (reachFin M q).card :=
          Finset.card_le_card (reachFin_subset hqr)
        have := ih hc
        omega

variable [Fintype A]

/-- The words of length at most `n` that are accepted from the state `q`. -/
noncomputable def accFin (M : DFA A σ) (q : σ) (n : ℕ) : Finset (List A) :=
  (wordsLE A n).filter fun w => M.evalFrom q w ∈ M.accept

/-- The number of words of length at most `n` that are accepted from the state `q`. -/
noncomputable def accCount (M : DFA A σ) (q : σ) (n : ℕ) : ℕ := (accFin M q n).card

omit [Fintype σ] in
lemma mem_accFin {q : σ} {n : ℕ} {w : List A} :
    w ∈ accFin M q n ↔ w.length ≤ n ∧ M.evalFrom q w ∈ M.accept := by
  simp [accFin]

omit [Fintype σ] in
lemma accFin_mono {q : σ} {m n : ℕ} (h : m ≤ n) : accFin M q m ⊆ accFin M q n := by
  intro w hw
  rw [mem_accFin] at hw ⊢
  exact ⟨le_trans hw.1 h, hw.2⟩

omit [Fintype σ] in
lemma accCount_mono {q : σ} {m n : ℕ} (h : m ≤ n) : accCount M q m ≤ accCount M q n :=
  Finset.card_le_card (accFin_mono h)

omit [Fintype σ] in
lemma accCount_eq_zero_of_not_useful {q : σ} (h : ¬ Useful M q) (n : ℕ) :
    accCount M q n = 0 := by
  rw [accCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  exact h ⟨w, (mem_accFin.mp hw).2⟩

end Aut

/-! ## The forced path inside a strongly connected component -/

section Forced

variable {A σ : Type}

/-- The states along the path that follows, from `q`, the letter chosen by `nxt`. -/
def loopState (M : DFA A σ) (nxt : σ → A) (q : σ) : ℕ → σ
  | 0 => q
  | t + 1 => M.step (loopState M nxt q t) (nxt (loopState M nxt q t))

/-- The word read along the path that follows, from `q`, the letter chosen by `nxt`. -/
def loopWord (M : DFA A σ) (nxt : σ → A) (q : σ) : ℕ → List A
  | 0 => []
  | t + 1 => loopWord M nxt q t ++ [nxt (loopState M nxt q t)]

variable (M : DFA A σ) (nxt : σ → A) (q : σ)

@[simp] lemma loopWord_zero : loopWord M nxt q 0 = [] := rfl

lemma loopWord_succ (t : ℕ) :
    loopWord M nxt q (t + 1) = loopWord M nxt q t ++ [nxt (loopState M nxt q t)] := rfl

lemma loopWord_length (t : ℕ) : (loopWord M nxt q t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [loopWord_succ, List.length_append, ih]; rfl

lemma evalFrom_loopWord (t : ℕ) : M.evalFrom q (loopWord M nxt q t) = loopState M nxt q t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [loopWord_succ, M.evalFrom_append_singleton, ih]
      rfl

@[simp] lemma loopState_one : loopState M nxt q 1 = M.step q (nxt q) := rfl

@[simp] lemma loopWord_one : loopWord M nxt q 1 = [nxt q] := rfl

lemma loopWord_add (t s : ℕ) :
    loopWord M nxt q (t + s) = loopWord M nxt q t ++ loopWord M nxt (loopState M nxt q t) s := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hst : loopState M nxt (loopState M nxt q t) s = loopState M nxt q (t + s) := by
        clear ih
        induction s with
        | zero => rfl
        | succ s ihs =>
            show M.step (loopState M nxt (loopState M nxt q t) s)
              (nxt (loopState M nxt (loopState M nxt q t) s)) = _
            rw [ihs]
            rfl
      have h1 : t + (s + 1) = (t + s) + 1 := by omega
      rw [h1, loopWord_succ, loopWord_succ, ih, hst, List.append_assoc]

lemma loopWord_cons (s : ℕ) :
    loopWord M nxt q (1 + s) = nxt q :: loopWord M nxt (M.step q (nxt q)) s := by
  rw [loopWord_add, loopWord_one, loopState_one]
  rfl

/-- Every word either follows the path forced by `nxt` all the way, or follows it for a while
and then leaves it. -/
lemma loopWord_decomp (w : List A) (t : ℕ) :
    (∃ s, w = loopWord M nxt (loopState M nxt q t) s) ∨
      (∃ (s : ℕ) (b : A) (z : List A), b ≠ nxt (loopState M nxt q (t + s)) ∧
        w = loopWord M nxt (loopState M nxt q t) s ++ b :: z) := by
  induction w generalizing t with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons a w' ihw =>
      by_cases ha : a = nxt (loopState M nxt q t)
      · subst ha
        rcases ihw (t + 1) with ⟨s, hs⟩ | ⟨s, b, z, hb, hz⟩
        · refine Or.inl ⟨1 + s, ?_⟩
          rw [loopWord_cons]
          exact congrArg _ hs
        · refine Or.inr ⟨1 + s, b, z, ?_, ?_⟩
          · have : t + (1 + s) = t + 1 + s := by omega
            rw [this]
            exact hb
          · rw [loopWord_cons]
            exact congrArg _ hz
      · exact Or.inr ⟨0, a, w', by simpa using ha, by simp⟩

end Forced

/-! ## The two bounds -/

section Bounds

variable {A σ : Type} [Fintype A] [Fintype σ] {M : DFA A σ}

/-- **The upper bound.**  If the automaton has no ambiguous cycle and no chain of `k+1` loops
from `q`, then the number of words of length at most `n` accepted from `q` is `O(n^k)`. -/
theorem accCount_le_of_not_chain (hamb : ¬ AmbCycle M) :
    ∀ (N : ℕ) (q : σ) (k : ℕ), (reachFin M q).card ≤ N → Reaches M M.start q →
      ¬ Chain M q (k + 1) → ∃ C : ℕ, ∀ n, accCount M q n ≤ C * (n + 1) ^ k := by
  classical
  intro N
  induction N with
  | zero =>
      intro q k hcard _ _
      have : 0 < (reachFin M q).card :=
        Finset.card_pos.mpr ⟨q, mem_reachFin.mpr (reaches_refl q)⟩
      omega
  | succ N ih =>
      intro q k hcard hreach hnot
      by_cases huse : Useful M q
      swap
      · exact ⟨0, fun n => by simp [accCount_eq_zero_of_not_useful huse n]⟩
      by_cases hloop : Loopy M q
      swap
      · -- no loop at `q`: every successor lies in a strictly smaller component
        have hstep : ∀ a : A, ∃ C : ℕ, ∀ n, accCount M (M.step q a) n ≤ C * (n + 1) ^ k := by
          intro a
          have hns : ¬ Reaches M (M.step q a) q := by
            rintro ⟨w, hw⟩
            exact hloop ⟨a :: w, by simp, hw⟩
          have hcr : (reachFin M (M.step q a)).card ≤ N := by
            have := reachFin_card_lt (reaches_step q a) hns
            omega
          refine ih _ k hcr (reaches_trans hreach (reaches_step q a)) ?_
          intro hc
          exact hnot (chain_of_reaches (reaches_step q a) hc)
        choose Ca hCa using hstep
        refine ⟨1 + ∑ a : A, Ca a, fun n => ?_⟩
        have hsub : accFin M q n ⊆
            insert ([] : List A)
              (Finset.univ.biUnion fun a : A => (accFin M (M.step q a) n).image (a :: ·)) := by
          intro w hw
          obtain ⟨hlen, hacc⟩ := mem_accFin.mp hw
          cases w with
          | nil => exact Finset.mem_insert_self _ _
          | cons a z =>
              refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, ?_⟩)
              exact Finset.mem_image.mpr ⟨z, mem_accFin.mpr
                ⟨by simpa using Nat.le_of_succ_le hlen, hacc⟩, rfl⟩
        have h1 : accCount M q n ≤ 1 + ∑ a : A, accCount M (M.step q a) n := by
          refine le_trans (Finset.card_le_card hsub) ?_
          refine le_trans (Finset.card_insert_le _ _) ?_
          have : (Finset.univ.biUnion fun a : A =>
              (accFin M (M.step q a) n).image (a :: ·)).card ≤ ∑ a : A, accCount M (M.step q a) n :=
            le_trans (Finset.card_biUnion_le)
              (Finset.sum_le_sum fun a _ => Finset.card_image_le)
          omega
        have h2 : ∑ a : A, accCount M (M.step q a) n ≤ (∑ a : A, Ca a) * (n + 1) ^ k := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun a _ => hCa a n
        have h3 : (1 : ℕ) ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
        calc accCount M q n ≤ 1 + ∑ a : A, accCount M (M.step q a) n := h1
          _ ≤ (n + 1) ^ k + (∑ a : A, Ca a) * (n + 1) ^ k := by omega
          _ = (1 + ∑ a : A, Ca a) * (n + 1) ^ k := by ring
      -- `q` lies on a loop
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · exact absurd (⟨q, reaches_refl q, hloop, Or.inl ⟨rfl, huse⟩⟩ : Chain M q 1) hnot
        · exact h
      have hA : Nonempty A := by
        obtain ⟨x, hxne, -⟩ := hloop
        cases x with
        | nil => exact absurd rfl hxne
        | cons a _ => exact ⟨a⟩
      have hex : ∀ p : σ, ∃ a : A,
          (Reaches M q p ∧ Reaches M p q) → Reaches M (M.step p a) p := by
        intro p
        by_cases hp : Reaches M q p ∧ Reaches M p q
        · obtain ⟨⟨v, hv⟩, ⟨u, hu⟩⟩ := hp
          obtain ⟨x, hxne, hx⟩ := hloop
          have hw : M.evalFrom p (u ++ x ++ v) = p := by
            rw [M.evalFrom_of_append, M.evalFrom_of_append, hu, hx, hv]
          have hwne : u ++ x ++ v ≠ [] := by
            intro h
            have := congrArg List.length h
            simp only [List.length_append, List.length_nil] at this
            have : 0 < x.length := List.length_pos_iff.mpr hxne
            omega
          match hcons : u ++ x ++ v, hwne with
          | a :: w', _ => exact ⟨a, fun _ => ⟨w', by rw [hcons] at hw; exact hw⟩⟩
        · exact ⟨Classical.arbitrary A, fun h => absurd h hp⟩
      choose nxt hnxt using hex
      have huniq : ∀ p : σ, Reaches M q p → Reaches M p q → ∀ b : A, b ≠ nxt p →
          ¬ Reaches M (M.step p b) p := by
        intro p h1 h2 b hb hcon
        obtain ⟨wa, hwa⟩ := hnxt p ⟨h1, h2⟩
        obtain ⟨wb, hwb⟩ := hcon
        refine hamb (ambCycle_of_two_loops (q := p) (reaches_trans hreach h1)
          (useful_of_reaches h2 huse) (x := nxt p :: wa) (y := b :: wb) hwa hwb
          (by simp) (by simp) ?_)
        simp only [List.head?_cons, ne_eq, Option.some.injEq]
        exact fun h => hb h.symm
      have hscc : ∀ t : ℕ,
          Reaches M q (loopState M nxt q t) ∧ Reaches M (loopState M nxt q t) q := by
        intro t
        induction t with
        | zero => exact ⟨reaches_refl q, reaches_refl q⟩
        | succ t iht =>
            obtain ⟨h1, h2⟩ := iht
            exact ⟨reaches_trans h1 (reaches_step _ _),
              reaches_trans (hnxt _ ⟨h1, h2⟩) h2⟩
      have hexit : ∀ (t : ℕ) (b : A), b ≠ nxt (loopState M nxt q t) →
          Reaches M q (M.step (loopState M nxt q t) b) ∧
            ¬ Reaches M (M.step (loopState M nxt q t) b) q := by
        intro t b hb
        obtain ⟨h1, h2⟩ := hscc t
        refine ⟨reaches_trans h1 (reaches_step _ _), fun hr => ?_⟩
        exact huniq _ h1 h2 b hb (reaches_trans hr h1)
      have hkey : ∀ r : σ, ∃ C : ℕ, (Reaches M q r ∧ ¬ Reaches M r q) →
          ∀ n, accCount M r n ≤ C * (n + 1) ^ (k - 1) := by
        intro r
        by_cases hr : Reaches M q r ∧ ¬ Reaches M r q
        · obtain ⟨h1, h2⟩ := hr
          have hcr : (reachFin M r).card ≤ N := by
            have := reachFin_card_lt h1 h2
            omega
          have hnc : ¬ Chain M r (k - 1 + 1) := by
            have hkk : k - 1 + 1 = k := by omega
            rw [hkk]
            intro hc
            exact hnot ⟨q, reaches_refl q, hloop, Or.inr ⟨r, h1, h2, hc⟩⟩
          obtain ⟨C, hC⟩ := ih r (k - 1) hcr (reaches_trans hreach h1) hnc
          exact ⟨C, fun _ => hC⟩
        · exact ⟨0, fun h => absurd h hr⟩
      choose Cf hCf using hkey
      refine ⟨1 + Fintype.card A * Finset.univ.sup Cf, fun n => ?_⟩
      set Cm := Finset.univ.sup Cf with hCm
      set big : Finset (List A) :=
        ((Finset.range (n + 1)).image (fun t => loopWord M nxt q t)) ∪
          (Finset.range (n + 1)).biUnion (fun t =>
            (Finset.univ.erase (nxt (loopState M nxt q t))).biUnion (fun b =>
              (accFin M (M.step (loopState M nxt q t) b) n).image
                (fun z => loopWord M nxt q t ++ b :: z))) with hbig
      have hsub : accFin M q n ⊆ big := by
        intro w hw
        obtain ⟨hlen, hacc⟩ := mem_accFin.mp hw
        have h0 : loopState M nxt q 0 = q := rfl
        rcases loopWord_decomp M nxt q w 0 with ⟨s, hs⟩ | ⟨s, b, z, hb, hz⟩
        · rw [h0] at hs
          refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, ?_, ?_⟩)
          · refine Finset.mem_range.mpr ?_
            have : w.length = s := by rw [hs]; exact loopWord_length M nxt q s
            omega
          · exact hs.symm
        · rw [h0] at hz
          refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, ?_, ?_⟩)
          · refine Finset.mem_range.mpr ?_
            have hl : w.length = s + (z.length + 1) := by
              rw [hz]
              simp [loopWord_length]
            omega
          · refine Finset.mem_biUnion.mpr ⟨b, ?_, ?_⟩
            · exact Finset.mem_erase.mpr ⟨by simpa using hb, Finset.mem_univ b⟩
            · refine Finset.mem_image.mpr ⟨z, mem_accFin.mpr ⟨?_, ?_⟩, ?_⟩
              · have hl : w.length = s + (z.length + 1) := by
                  rw [hz]
                  simp [loopWord_length]
                omega
              · have := hacc
                rw [hz] at this
                rw [M.evalFrom_of_append, evalFrom_loopWord] at this
                exact this
              · exact hz.symm
      have hcard1 : ((Finset.range (n + 1)).image (fun t => loopWord M nxt q t)).card ≤ n + 1 := by
        refine le_trans Finset.card_image_le ?_
        simp
      have hinner : ∀ t : ℕ,
          ((Finset.univ.erase (nxt (loopState M nxt q t))).biUnion (fun b =>
            (accFin M (M.step (loopState M nxt q t) b) n).image
              (fun z => loopWord M nxt q t ++ b :: z))).card
            ≤ Fintype.card A * (Cm * (n + 1) ^ (k - 1)) := by
        intro t
        refine le_trans Finset.card_biUnion_le ?_
        refine le_trans (Finset.sum_le_sum (g := fun _ : A => Cm * (n + 1) ^ (k - 1))
          (fun b hb => ?_)) ?_
        · refine le_trans Finset.card_image_le ?_
          have hbne : b ≠ nxt (loopState M nxt q t) := (Finset.mem_erase.mp hb).1
          have hb' := hexit t b hbne
          refine le_trans (hCf _ hb' n) ?_
          have : Cf (M.step (loopState M nxt q t) b) ≤ Cm := Finset.le_sup (Finset.mem_univ _)
          exact Nat.mul_le_mul_right _ this
        · rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _
            (le_trans (Finset.card_erase_le) (le_of_eq (Finset.card_univ)))
      have hcard2 : ((Finset.range (n + 1)).biUnion (fun t =>
            (Finset.univ.erase (nxt (loopState M nxt q t))).biUnion (fun b =>
              (accFin M (M.step (loopState M nxt q t) b) n).image
                (fun z => loopWord M nxt q t ++ b :: z)))).card
          ≤ (n + 1) * (Fintype.card A * (Cm * (n + 1) ^ (k - 1))) := by
        refine le_trans Finset.card_biUnion_le ?_
        refine le_trans (Finset.sum_le_sum
          (g := fun _ : ℕ => Fintype.card A * (Cm * (n + 1) ^ (k - 1)))
          (fun t _ => hinner t)) ?_
        rw [Finset.sum_const, smul_eq_mul, Finset.card_range]
      have hpow : (n + 1) * (n + 1) ^ (k - 1) = (n + 1) ^ k := by
        rw [← pow_succ']
        congr 1
        omega
      have hle1 : (n + 1) ≤ (n + 1) ^ k := by
        calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
          _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (by omega) hk1
      calc accCount M q n ≤ big.card := Finset.card_le_card hsub
        _ ≤ (n + 1) + (n + 1) * (Fintype.card A * (Cm * (n + 1) ^ (k - 1))) :=
            le_trans (Finset.card_union_le _ _) (Nat.add_le_add hcard1 hcard2)
        _ = (n + 1) + Fintype.card A * Cm * ((n + 1) * (n + 1) ^ (k - 1)) := by ring
        _ = (n + 1) + Fintype.card A * Cm * (n + 1) ^ k := by rw [hpow]
        _ ≤ (n + 1) ^ k + Fintype.card A * Cm * (n + 1) ^ k := by omega
        _ = (1 + Fintype.card A * Cm) * (n + 1) ^ k := by ring

omit [Fintype A] [Fintype σ] in
/-- The words obtained by pumping a loop and then reading a word that leaves its strongly
connected component are pairwise distinct: this is the shifting lemma
`Transducers.Exercises.RegGrowth.reaches_of_loop_shift`. -/
lemma loop_words_inj {r r' : σ} {x u : List A} (hx : M.evalFrom r x = r) (hxne : x ≠ [])
    (hu : M.evalFrom r u = r') (hnot : ¬ Reaches M r' r) {u₀ : List A} {i j : ℕ} {v v' : List A}
    (heq : u₀ ++ loopPow x i ++ u ++ v = u₀ ++ loopPow x j ++ u ++ v') : i = j ∧ v = v' := by
  have hcancel : loopPow x i ++ (u ++ v) = loopPow x j ++ (u ++ v') := by
    refine List.append_cancel_left (as := u₀) ?_
    simpa [List.append_assoc] using heq
  have hij : i = j := by
    by_contra hne
    rcases Nat.lt_or_ge i j with hlt | hge
    · have hsplit : loopPow x j = loopPow x i ++ loopPow x (j - i) := by
        rw [← loopPow_add]
        congr 1
        omega
      rw [hsplit, List.append_assoc] at hcancel
      have hcc := List.append_cancel_left hcancel
      have h2 : u ++ v = loopPow x (j - i) ++ u ++ v' := by
        simpa [List.append_assoc] using hcc
      exact hnot (reaches_of_loop_shift hx hxne u hu (j - i) (by omega) v v' h2)
    · have hlt : j < i := by omega
      have hsplit : loopPow x i = loopPow x j ++ loopPow x (i - j) := by
        rw [← loopPow_add]
        congr 1
        omega
      rw [hsplit, List.append_assoc] at hcancel
      have hcc := List.append_cancel_left hcancel.symm
      have h2 : u ++ v' = loopPow x (i - j) ++ u ++ v := by
        simpa [List.append_assoc] using hcc
      exact hnot (reaches_of_loop_shift hx hxne u hu (i - j) (by omega) v' v h2)
  subst hij
  exact ⟨rfl, List.append_cancel_left (List.append_cancel_left hcancel)⟩

omit [Fintype σ] in
/-- **The lower bound.**  A chain of `k` loops from `q` produces `Ω(n^k)` words of length at
most `n` accepted from `q`. -/
theorem chain_lower_bound {q : σ} {k : ℕ} (h : Chain M q k) :
    ∃ c : ℕ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n → (n + 1) ^ k ≤ c * accCount M q n := by
  induction k generalizing q with
  | zero =>
      obtain ⟨w, hw⟩ := h
      refine ⟨1, one_pos, w.length, fun n hn => ?_⟩
      have hmem : w ∈ accFin M q n := mem_accFin.mpr ⟨hn, hw⟩
      have hpos : 0 < accCount M q n := Finset.card_pos.mpr ⟨w, hmem⟩
      simpa using hpos
  | succ k ih =>
      obtain ⟨r, ⟨u₀, hu₀⟩, ⟨x, hxne, hx⟩, hrest⟩ := h
      have hxpos : 0 < x.length := List.length_pos_iff.mpr hxne
      rcases hrest with ⟨rfl, ⟨u, hu⟩⟩ | ⟨r', ⟨u, hu⟩, hnot, hc⟩
      · -- the last loop: `u₀ x^i u` is accepted for every `i`
        refine ⟨2 * x.length, by omega, 2 * (u₀.length + u.length) + 2, fun n hn => ?_⟩
        obtain ⟨I, hIdef⟩ : ∃ I, I = (n - (u₀.length + u.length)) / x.length := ⟨_, rfl⟩
        have hIl : I * x.length ≤ n - (u₀.length + u.length) := by
          rw [hIdef]; exact Nat.div_mul_le_self _ _
        have hIl2 : n - (u₀.length + u.length) < (I + 1) * x.length := by
          rw [hIdef]
          exact (Nat.div_lt_iff_lt_mul hxpos).mp (Nat.lt_succ_self _)
        have hcard : I + 1 ≤ accCount M q n := by
          have hsub : (Finset.range (I + 1)).card ≤ (accFin M q n).card := by
            refine Finset.card_le_card_of_injOn (fun i => u₀ ++ loopPow x i ++ u) ?_ ?_
            · intro i hi
              simp only [Finset.coe_range, Set.mem_Iio] at hi
              refine Finset.mem_coe.mpr (mem_accFin.mpr ⟨?_, ?_⟩)
              · have hile : i * x.length ≤ I * x.length :=
                  Nat.mul_le_mul_right _ (by omega)
                simp only [List.length_append, loopPow_length]
                omega
              · rw [M.evalFrom_of_append, M.evalFrom_of_append, hu₀, evalFrom_loopPow hx]
                exact hu
            · intro i _ j _ hij
              have hlen := congrArg List.length hij
              simp only [List.length_append, loopPow_length] at hlen
              have : i * x.length = j * x.length := by omega
              exact Nat.eq_of_mul_eq_mul_right hxpos this
          simpa using hsub
        have h2 : n + 1 ≤ 2 * ((I + 1) * x.length) := by
          have key : ∀ P : ℕ, n - (u₀.length + u.length) < P → n + 1 ≤ 2 * P := by
            intro P hP; omega
          exact key _ hIl2
        calc (n + 1) ^ (0 + 1) = n + 1 := by ring
          _ ≤ 2 * ((I + 1) * x.length) := h2
          _ = 2 * x.length * (I + 1) := by ring
          _ ≤ 2 * x.length * accCount M q n := by gcongr
      · -- a loop, an exit, and a shorter chain
        obtain ⟨c, hcpos, N, hN⟩ := ih hc
        have hcpos' : 0 < 2 ^ k * 4 * x.length * c :=
          Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos (by norm_num) k) (by norm_num)) hxpos)
            hcpos
        refine ⟨2 ^ k * 4 * x.length * c, hcpos',
          max (2 * N) (4 * (u₀.length + u.length) + 4), fun n hn => ?_⟩
        have hn1 : 2 * N ≤ n := le_trans (le_max_left _ _) hn
        have hn2 : 4 * (u₀.length + u.length) + 4 ≤ n := le_trans (le_max_right _ _) hn
        obtain ⟨m, hmdef⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
        obtain ⟨I, hIdef⟩ : ∃ I, I = (n - (u₀.length + u.length) - m) / x.length := ⟨_, rfl⟩
        have hIl : I * x.length ≤ n - (u₀.length + u.length) - m := by
          rw [hIdef]; exact Nat.div_mul_le_self _ _
        have hIl2 : n - (u₀.length + u.length) - m < (I + 1) * x.length := by
          rw [hIdef]
          exact (Nat.div_lt_iff_lt_mul hxpos).mp (Nat.lt_succ_self _)
        have hmN : N ≤ m := by omega
        have hcard : (I + 1) * accCount M r' m ≤ accCount M q n := by
          have hsub : ((Finset.range (I + 1)) ×ˢ (accFin M r' m)).card ≤ (accFin M q n).card := by
            refine Finset.card_le_card_of_injOn
              (fun p => u₀ ++ loopPow x p.1 ++ u ++ p.2) ?_ ?_
            · rintro ⟨i, v⟩ hiv
              rw [Finset.coe_product, Set.mem_prod] at hiv
              obtain ⟨hi, hv⟩ := hiv
              simp only [Finset.coe_range, Set.mem_Iio] at hi
              have hv' := mem_accFin.mp (Finset.mem_coe.mp hv)
              refine Finset.mem_coe.mpr (mem_accFin.mpr ⟨?_, ?_⟩)
              · have hile : i * x.length ≤ I * x.length :=
                  Nat.mul_le_mul_right _ (by omega)
                have hvl : v.length ≤ m := hv'.1
                simp only [List.length_append, loopPow_length]
                omega
              · rw [M.evalFrom_of_append, M.evalFrom_of_append, M.evalFrom_of_append,
                  hu₀, evalFrom_loopPow hx, hu]
                exact hv'.2
            · rintro ⟨i, v⟩ - ⟨j, v'⟩ - heq
              obtain ⟨h1, h2⟩ := loop_words_inj hx hxne hu hnot heq
              exact Prod.ext h1 h2
          rw [Finset.card_product, Finset.card_range] at hsub
          exact hsub
        have hlow : (m + 1) ^ k ≤ c * accCount M r' m := hN m hmN
        have h2m : n + 1 ≤ 2 * (m + 1) := by omega
        have h4 : n + 1 ≤ 4 * ((I + 1) * x.length) := by
          have key : ∀ P : ℕ, n - (u₀.length + u.length) - m < P → n + 1 ≤ 4 * P := by
            intro P hP; omega
          exact key _ hIl2
        calc (n + 1) ^ (k + 1) = (n + 1) ^ k * (n + 1) := by ring
          _ ≤ (2 * (m + 1)) ^ k * (4 * ((I + 1) * x.length)) :=
              Nat.mul_le_mul (Nat.pow_le_pow_left h2m k) h4
          _ = 2 ^ k * ((m + 1) ^ k) * (4 * ((I + 1) * x.length)) := by rw [mul_pow]
          _ ≤ 2 ^ k * (c * accCount M r' m) * (4 * ((I + 1) * x.length)) := by gcongr
          _ = 2 ^ k * 4 * x.length * c * ((I + 1) * accCount M r' m) := by ring
          _ ≤ 2 ^ k * 4 * x.length * c * accCount M q n := by gcongr

end Bounds

end RegGrowth

/-! ## The growth gap theorem -/

/-- **The growth gap theorem for regular languages.**  For a nonempty regular language over a
finite alphabet, either the number of words of length at most `n` is super-polynomial — and then
the language contains a whole binary tree of words, obtained by following two loops of the same
length with different labels — or it is `Θ(n^k)` for some `k`. -/
theorem regular_growth_dichotomy {A : Type} [Finite A] {L : Language A} (hL : L.IsRegular)
    (hne : ∃ w, w ∈ L) :
    (∃ p x y s : List A, 0 < x.length ∧ x.length = y.length ∧ x ≠ y ∧
        ∀ u : List Bool, p ++ Transducers.cycleWord x y u ++ s ∈ L) ∨
      (∃ k : ℕ, (∃ C : ℕ, ∀ n, langCount L n ≤ C * (n + 1) ^ k) ∧
        ∃ c : ℕ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n → (n + 1) ^ k ≤ c * langCount L n) := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  obtain ⟨σ, hσ, M, hM⟩ := hL
  subst hM
  have hcount : ∀ n, langCount M.accepts n = RegGrowth.accCount M M.start n := by
    intro n
    rw [langCount, RegGrowth.accCount, ← Set.ncard_coe_finset]
    congr 1
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact Finset.mem_coe.mpr (RegGrowth.mem_accFin.mpr ⟨h2, h1⟩)
    · intro h
      have h' := RegGrowth.mem_accFin.mp (Finset.mem_coe.mp h)
      exact ⟨h'.2, h'.1⟩
  by_cases hamb : RegGrowth.AmbCycle M
  · left
    obtain ⟨q, ⟨pw, hp⟩, ⟨sw, hs⟩, x, y, hlen, hxy, hx, hy⟩ := hamb
    have hxpos : 0 < x.length := by
      rcases Nat.eq_zero_or_pos x.length with h | h
      · exfalso
        rw [List.length_eq_zero_iff] at h
        have hy0 : y = [] := by
          rw [← List.length_eq_zero_iff, ← hlen, h]
          rfl
        exact hxy (h.trans hy0.symm)
      · exact h
    refine ⟨pw, x, y, sw, hxpos, hlen, hxy, fun u => ?_⟩
    have hcyc : M.evalFrom q (Transducers.cycleWord x y u) = q := by
      induction u with
      | nil => rfl
      | cons b u ih =>
          cases b
          · rw [Transducers.cycleWord_cons_false, M.evalFrom_of_append, hy, ih]
          · rw [Transducers.cycleWord_cons_true, M.evalFrom_of_append, hx, ih]
    show M.evalFrom M.start (pw ++ Transducers.cycleWord x y u ++ sw) ∈ M.accept
    rw [M.evalFrom_of_append, M.evalFrom_of_append, hp, hcyc]
    exact hs
  · right
    obtain ⟨w₀, hw₀⟩ := hne
    have h0 : RegGrowth.Chain M M.start 0 := ⟨w₀, hw₀⟩
    obtain ⟨k, hkspec, hknot⟩ : ∃ k : ℕ, RegGrowth.Chain M M.start k ∧
        ¬ RegGrowth.Chain M M.start (k + 1) := by
      refine ⟨Nat.findGreatest (fun j => RegGrowth.Chain M M.start j) (Fintype.card σ),
        Nat.findGreatest_spec (Nat.zero_le _) h0, fun hc => ?_⟩
      have h1 := RegGrowth.chain_card_le hc
      have h2 : (RegGrowth.reachFin M M.start).card ≤ Fintype.card σ := Finset.card_le_univ _
      exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (by omega) hc
    obtain ⟨C, hC⟩ := RegGrowth.accCount_le_of_not_chain hamb (Fintype.card σ) M.start k
      (Finset.card_le_univ _) (RegGrowth.reaches_refl _) hknot
    obtain ⟨c, hcpos, N, hN⟩ := RegGrowth.chain_lower_bound hkspec
    exact ⟨k, ⟨C, fun n => by rw [hcount]; exact hC n⟩,
      c, hcpos, N, fun n hn => by rw [hcount]; exact hN n hn⟩

end Transducers.Exercises
