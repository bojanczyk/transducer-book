/-
Sorted words over a `k`-letter alphabet, and the rational function that turns a sorted word into
the corresponding word of a `k`-pattern.
-/
import RequestProject.Exercises.ChainWords
import RequestProject.Exercises.SeqSST
import RequestProject.PartC.RatTools

/-!
# Sorted words and the words of a `k`-pattern

The function `f_k` of the author's solution to Exercise `exer:polynomial-ideals` is the identity
on the *sorted* words of `{a_1, …, a_k}*` — those of `a_1^* a_2^* ⋯ a_k^*` — and the empty word
elsewhere; it is `Transducers.Exercises.sortedFun` here.  This file provides what is needed about
it and about the `k`-patterns of `RequestProject/Exercises/ChainWords.lean`:

* `Transducers.Exercises.cnt` — the number of occurrences of a letter in a word, and
  `Transducers.Exercises.sorted_eq_of_cnt`: a sorted word is determined by the numbers of
  occurrences of its letters;
* `Transducers.Exercises.sortedFun`, `Transducers.Exercises.isRationalFun_sortedFun` — the
  function `f_k` is rational (a contextual rewriting, whose mode is the state of the automaton
  that checks that the word is sorted), and it is a retraction onto the sorted words;
* `Transducers.Exercises.patTail`, `Transducers.Exercises.chainWord_eq_patTail` — the words of a
  `k`-pattern, written as a recursion on the index of the block rather than as a recursion on the
  chain;
* `Transducers.Exercises.patEmit` — the sequential rewriting with a final output that turns a
  sorted word `a_1^{c_1} ⋯ a_k^{c_k}` into the word `us 0 · (xs 0)^{c_1} · us 1 ⋯ us k` of the
  pattern; it is rational, and injective on the sorted words as soon as the pattern determines
  its exponents (`Transducers.Exercises.patEmit_injOn_sorted`).
-/

namespace Transducers.Exercises

open Transducers

/-! ### Counting the letters of a word -/

/-- The number of occurrences of the letter of index `i` in `v`. -/
def cnt {k : ℕ} : List (Fin k) → ℕ → ℕ
  | [], _ => 0
  | a :: v, i => cnt v i + if i = (a : ℕ) then 1 else 0

@[simp] lemma cnt_nil {k : ℕ} (i : ℕ) : cnt ([] : List (Fin k)) i = 0 := rfl

lemma cnt_cons {k : ℕ} (a : Fin k) (v : List (Fin k)) (i : ℕ) :
    cnt (a :: v) i = cnt v i + if i = (a : ℕ) then 1 else 0 := rfl

@[simp] lemma cnt_cons_self {k : ℕ} (a : Fin k) (v : List (Fin k)) :
    cnt (a :: v) (a : ℕ) = cnt v (a : ℕ) + 1 := by
  rw [cnt_cons, if_pos rfl]

lemma cnt_cons_of_ne {k : ℕ} {a : Fin k} {i : ℕ} (h : i ≠ (a : ℕ)) (v : List (Fin k)) :
    cnt (a :: v) i = cnt v i := by
  rw [cnt_cons, if_neg h, Nat.add_zero]

/-- A letter that does not occur in `v` is counted `0` times. -/
lemma cnt_eq_zero {k : ℕ} {v : List (Fin k)} {i : ℕ} (h : ∀ a ∈ v, i ≠ (a : ℕ)) :
    cnt v i = 0 := by
  induction v with
  | nil => rfl
  | cons a v ih =>
      rw [cnt_cons_of_ne (h a (List.mem_cons_self ..)) v]
      exact ih fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- Letters outside the alphabet are counted `0` times. -/
lemma cnt_eq_zero_of_le {k : ℕ} (v : List (Fin k)) {i : ℕ} (h : k ≤ i) : cnt v i = 0 :=
  cnt_eq_zero fun a _ => by have := a.isLt; omega

/-- **A sorted word is determined by the numbers of occurrences of its letters.** -/
lemma sorted_eq_of_cnt {k : ℕ} : ∀ {v v' : List (Fin k)}, v.Pairwise (· ≤ ·) →
    v'.Pairwise (· ≤ ·) → (∀ i, cnt v i = cnt v' i) → v = v' := by
  intro v
  induction v with
  | nil =>
      intro v' _ _ h
      cases v' with
      | nil => rfl
      | cons b t =>
          have := h (b : ℕ)
          rw [cnt_nil, cnt_cons_self] at this
          omega
  | cons a t ih =>
      intro v' hv hv' h
      cases v' with
      | nil =>
          have := h (a : ℕ)
          rw [cnt_nil, cnt_cons_self] at this
          omega
      | cons b t' =>
          rw [List.pairwise_cons] at hv hv'
          have hab : a = b := by
            by_contra hne
            rcases lt_or_gt_of_ne (fun hval : (a : ℕ) = (b : ℕ) => hne (Fin.ext hval)) with
              hlt | hlt
            · have h1 : cnt (a :: t) (a : ℕ) = cnt t (a : ℕ) + 1 := cnt_cons_self a t
              have h2 : cnt (b :: t') (a : ℕ) = 0 := by
                refine cnt_eq_zero fun c hc => ?_
                rcases List.mem_cons.mp hc with rfl | hc'
                · omega
                · have := hv'.1 c hc'
                  have : (b : ℕ) ≤ (c : ℕ) := this
                  omega
              have := h (a : ℕ)
              omega
            · have h1 : cnt (b :: t') (b : ℕ) = cnt t' (b : ℕ) + 1 := cnt_cons_self b t'
              have h2 : cnt (a :: t) (b : ℕ) = 0 := by
                refine cnt_eq_zero fun c hc => ?_
                rcases List.mem_cons.mp hc with rfl | hc'
                · omega
                · have := hv.1 c hc'
                  have : (a : ℕ) ≤ (c : ℕ) := this
                  omega
              have := h (b : ℕ)
              omega
          subst hab
          have hcnt : ∀ i, cnt t i = cnt t' i := by
            intro i
            have := h i
            rw [cnt_cons, cnt_cons] at this
            omega
          rw [ih hv.2 hv'.2 hcnt]

/-! ### The sorted-identity function -/

/-- The state of the automaton that checks that a word is sorted: the last letter read, and
whether the word read so far is sorted. -/
def sortedOk {k : ℕ} : Option (Fin k) → Fin k → Bool
  | none, _ => true
  | some b, a => decide (b ≤ a)

/-- The step of the automaton that checks that a word is sorted. -/
def sortedStep (k : ℕ) : Option (Fin k) × Bool → Fin k → Option (Fin k) × Bool :=
  fun s a => (some a, s.2 && sortedOk s.1 a)

/-- `v` is sorted and all its letters are at least the last letter read. -/
def SortedFrom {k : ℕ} (l : Option (Fin k)) (v : List (Fin k)) : Prop :=
  v.Pairwise (· ≤ ·) ∧ ∀ b ∈ l, ∀ a ∈ v, b ≤ a

lemma sortedFrom_nil {k : ℕ} (l : Option (Fin k)) : SortedFrom l ([] : List (Fin k)) :=
  ⟨List.Pairwise.nil, fun _ _ _ ha => absurd ha (List.not_mem_nil)⟩

lemma sortedFrom_cons {k : ℕ} (l : Option (Fin k)) (a : Fin k) (v : List (Fin k)) :
    SortedFrom l (a :: v) ↔ (∀ b ∈ l, b ≤ a) ∧ SortedFrom (some a) v := by
  constructor
  · rintro ⟨hp, hl⟩
    rw [List.pairwise_cons] at hp
    exact ⟨fun b hb => hl b hb a (List.mem_cons_self ..), hp.2, fun b hb c hc => by
      cases hb
      exact hp.1 c hc⟩
  · rintro ⟨hla, hp, ha⟩
    refine ⟨List.pairwise_cons.mpr ⟨fun c hc => ha a rfl c hc, hp⟩, fun b hb c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hla b hb
    · exact le_trans (hla b hb) (ha a rfl c hc')

/-- The automaton accepts exactly the words that are sorted and start above the last letter
read. -/
lemma sortedStep_snd {k : ℕ} : ∀ (v : List (Fin k)) (l : Option (Fin k)) (b : Bool),
    (strTrans (sortedStep k) v (l, b)).2 = true ↔ (b = true ∧ SortedFrom l v) := by
  intro v
  induction v with
  | nil =>
      intro l b
      simp [strTrans, sortedFrom_nil]
  | cons a v ih =>
      intro l b
      have hstep : strTrans (sortedStep k) (a :: v) (l, b)
          = strTrans (sortedStep k) v (sortedStep k (l, b) a) := by
        simp [strTrans]
      rw [hstep]
      have hs : sortedStep k (l, b) a = (some a, b && sortedOk l a) := rfl
      rw [hs, ih, sortedFrom_cons]
      constructor
      · rintro ⟨hb, hv⟩
        rw [Bool.and_eq_true] at hb
        refine ⟨hb.1, fun c hc => ?_, hv⟩
        cases hc
        simpa [sortedOk] using hb.2
      · rintro ⟨hb, hla, hv⟩
        refine ⟨?_, hv⟩
        rw [Bool.and_eq_true]
        refine ⟨hb, ?_⟩
        cases l with
        | none => rfl
        | some c => simpa [sortedOk] using hla c rfl

open scoped Classical in
/-- The function `f_k` of the solution to Exercise `exer:polynomial-ideals`: the identity on the
sorted strings — those of `a_1^* a_2^* ⋯ a_k^*` — and the empty string on all other inputs. -/
noncomputable def sortedFun (k : ℕ) (w : List (Fin k)) : List (Fin k) :=
  if w.Pairwise (· ≤ ·) then w else []

open scoped Classical in
lemma sortedFun_of_sorted {k : ℕ} {w : List (Fin k)} (h : w.Pairwise (· ≤ ·)) :
    sortedFun k w = w := if_pos h

open scoped Classical in
/-- The value of `f_k` is always sorted. -/
lemma sortedFun_sorted {k : ℕ} (w : List (Fin k)) : (sortedFun k w).Pairwise (· ≤ ·) := by
  by_cases h : w.Pairwise (· ≤ ·)
  · rw [sortedFun_of_sorted h]; exact h
  · rw [sortedFun, if_neg h]; exact List.Pairwise.nil

/-- `f_k` is a retraction onto the sorted words. -/
lemma sortedFun_idem {k : ℕ} (w : List (Fin k)) : sortedFun k (sortedFun k w) = sortedFun k w :=
  sortedFun_of_sorted (sortedFun_sorted w)

/-- **The sorted-identity function is rational.**  It is a contextual rewriting: the mode is the
state of the automaton that checks that the input is sorted, and every letter is copied when the
mode says the input is sorted, and deleted otherwise. -/
theorem isRationalFun_sortedFun (k : ℕ) : IsRationalFun (sortedFun k) := by
  classical
  set ψ : (Option (Fin k) × Bool) → Option (Fin k) → Option (Fin k) → List (Fin k) :=
    fun m _ next => if m.2 = true then (match next with | none => [] | some a => [a]) else []
    with hψ
  have hcopy : ∀ (m : Option (Fin k) × Bool), m.2 = true →
      ∀ (w : List (Fin k)) (prev : Option (Fin k)), ctxAux (ψ m) prev w = w := by
    intro m hm w
    induction w with
    | nil => intro prev; simp [hψ, hm]
    | cons a w ih =>
        intro prev
        rw [ctxAux_cons, ih (some a)]
        simp [hψ, hm]
  have hdel : ∀ (m : Option (Fin k) × Bool), m.2 = false →
      ∀ (w : List (Fin k)) (prev : Option (Fin k)), ctxAux (ψ m) prev w = [] := by
    intro m hm w
    induction w with
    | nil => intro prev; simp [hψ, hm]
    | cons a w ih =>
        intro prev
        rw [ctxAux_cons, ih (some a)]
        simp [hψ, hm]
  have hval : ∀ w : List (Fin k),
      ctxEval (sortedStep k) (none, true) ψ w = sortedFun k w := by
    intro w
    rw [ctxEval]
    by_cases hs : w.Pairwise (· ≤ ·)
    · have hm : (strTrans (sortedStep k) w (none, true)).2 = true :=
        (sortedStep_snd w none true).mpr ⟨rfl, hs, fun b hb => absurd hb (by simp)⟩
      rw [hcopy _ hm w none, sortedFun_of_sorted hs]
    · have hm : (strTrans (sortedStep k) w (none, true)).2 = false := by
        by_contra hne
        have hm' : (strTrans (sortedStep k) w (none, true)).2 = true := by
          cases h : (strTrans (sortedStep k) w (none, true)).2 with
          | false => exact absurd h hne
          | true => rfl
        exact hs ((sortedStep_snd w none true).mp hm').2.1
      rw [hdel _ hm w none, sortedFun, if_neg hs]
  have := isRationalFun_ctxEval (sortedStep k) ((none, true) : Option (Fin k) × Bool) ψ
  exact (funext hval : ctxEval (sortedStep k) (none, true) ψ = sortedFun k) ▸ this

/-! ### The words of a `k`-pattern, block by block -/

section Pattern

variable {B : Type}

/-- The concatenation `us i · us (i+1) ⋯ us (j-1)` of the separators between the blocks `i` and
`j` of a pattern. -/
def sepRun (us : ℕ → List B) (i j : ℕ) : List B :=
  ((List.range (j - i)).map (fun t => us (i + t))).flatten

@[simp] lemma sepRun_self (us : ℕ → List B) (i : ℕ) : sepRun us i i = [] := by
  simp [sepRun]

lemma sepRun_of_le (us : ℕ → List B) {i j : ℕ} (h : j ≤ i) : sepRun us i j = [] := by
  simp [sepRun, Nat.sub_eq_zero_of_le h]

lemma sepRun_succ_right (us : ℕ → List B) {i j : ℕ} (h : i ≤ j) :
    sepRun us i (j + 1) = sepRun us i j ++ us j := by
  have hsub : j + 1 - i = (j - i) + 1 := by omega
  rw [sepRun, sepRun, hsub, List.range_succ]
  simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  congr 2
  omega

/-- The suffix of a pattern word from the block `i` on, with `n` blocks left to write. -/
def patTailAux (us xs : ℕ → List B) (k : ℕ) (c : ℕ → ℕ) : ℕ → ℕ → List B
  | 0, _ => us k
  | (n + 1), i =>
      if i < k then us i ++ RegGrowth.loopPow (xs i) (c i) ++ patTailAux us xs k c n (i + 1)
      else us k

/-- The suffix of a pattern word from the block `i` on: `us i · (xs i)^(c i) ⋯ us k`. -/
def patTail (us xs : ℕ → List B) (k i : ℕ) (c : ℕ → ℕ) : List B :=
  patTailAux us xs k c (k - i) i

lemma patTail_of_le (us xs : ℕ → List B) {k i : ℕ} (h : k ≤ i) (c : ℕ → ℕ) :
    patTail us xs k i c = us k := by
  have hk : k - i = 0 := by omega
  rw [patTail, hk, patTailAux]

lemma patTail_lt (us xs : ℕ → List B) {k i : ℕ} (h : i < k) (c : ℕ → ℕ) :
    patTail us xs k i c
      = us i ++ RegGrowth.loopPow (xs i) (c i) ++ patTail us xs k (i + 1) c := by
  have hk : k - i = (k - (i + 1)) + 1 := by omega
  rw [patTail, hk, patTailAux, if_pos h, patTail]

lemma patTail_congr (us xs : ℕ → List B) (k : ℕ) :
    ∀ (n i : ℕ), k - i ≤ n → ∀ c c' : ℕ → ℕ, (∀ t, i ≤ t → t < k → c t = c' t) →
      patTail us xs k i c = patTail us xs k i c' := by
  intro n
  induction n with
  | zero =>
      intro i hi c c' _
      rw [patTail_of_le us xs (by omega), patTail_of_le us xs (by omega)]
  | succ n ih =>
      intro i hi c c' h
      by_cases hik : i < k
      · rw [patTail_lt us xs hik, patTail_lt us xs hik, h i le_rfl hik,
          ih (i + 1) (by omega) c c' (fun t ht ht' => h t (by omega) ht')]
      · rw [patTail_of_le us xs (by omega), patTail_of_le us xs (by omega)]

/-- Blocks that are taken zero times contribute only their separators. -/
lemma patTail_skip (us xs : ℕ → List B) (k : ℕ) (c : ℕ → ℕ) {i : ℕ} :
    ∀ {j : ℕ}, i ≤ j → j ≤ k → (∀ t, i ≤ t → t < j → c t = 0) →
      patTail us xs k i c = sepRun us i j ++ patTail us xs k j c := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => intro _ _; simp
  | succ j hij ih =>
      intro hjk hzero
      have hlt : j < k := by omega
      rw [ih (by omega) (fun t ht ht' => hzero t ht (by omega)),
        patTail_lt us xs hlt, hzero j hij (by omega)]
      simp only [RegGrowth.loopPow_zero, List.append_nil]
      rw [sepRun_succ_right us hij]
      simp [List.append_assoc]

/-- A pattern whose blocks are all taken zero times is the concatenation of its separators. -/
lemma patTail_zero (us xs : ℕ → List B) {k i : ℕ} (hik : i ≤ k) (c : ℕ → ℕ)
    (hc : ∀ t, i ≤ t → t < k → c t = 0) :
    patTail us xs k i c = sepRun us i (k + 1) := by
  rw [patTail_skip us xs k c hik le_rfl hc, patTail_of_le us xs le_rfl,
    sepRun_succ_right us hik]

/-- The words of a chain of loops, written block by block. -/
lemma chainWord_eq_patTail_aux (us xs : ℕ → List B) :
    ∀ (k i : ℕ) (c : ℕ → ℕ), patTail us xs (i + k) i c
      = chainWord (fun t => us (i + t)) (fun t => xs (i + t)) k (fun t => c (i + t)) := by
  intro k
  induction k with
  | zero =>
      intro i c
      rw [patTail_of_le us xs (by omega)]
      simp
  | succ k ih =>
      intro i c
      have hlt : i < i + (k + 1) := by omega
      rw [patTail_lt us xs hlt, chainWord_succ]
      have harg : i + (k + 1) = (i + 1) + k := by omega
      rw [harg, ih (i + 1) c]
      have h1 : (fun t => us (i + 1 + t)) = fun t => us (i + (t + 1)) := by
        funext t; congr 1; omega
      have h2 : (fun t => xs (i + 1 + t)) = fun t => xs (i + (t + 1)) := by
        funext t; congr 1; omega
      have h3 : (fun t => c (i + 1 + t)) = fun t => c (i + (t + 1)) := by
        funext t; congr 1; omega
      rw [h1, h2, h3]
      simp

lemma chainWord_eq_patTail (us xs : ℕ → List B) (k : ℕ) (c : ℕ → ℕ) :
    chainWord us xs k c = patTail us xs k 0 c := by
  have h := chainWord_eq_patTail_aux us xs k 0 c
  simpa using h.symm

/-! ### The rational function that writes the word of a pattern -/

/-- The index of the first block that has not been written yet. -/
def patIdx {k : ℕ} : Option (Fin k) → ℕ
  | none => 0
  | some b => (b : ℕ) + 1

/-- The sequential rewriting that turns a sorted word into the corresponding word of the pattern
given by the separators `us` and the loops `xs`: reading the letter `a` writes the separators of
the blocks that are skipped, and one copy of the loop `xs a`. -/
noncomputable def patEmit (us xs : ℕ → List B) (k : ℕ) : List (Fin k) → List B :=
  seqFinEval (fun (_ : Option (Fin k)) (a : Fin k) => (some a : Option (Fin k)))
    (fun l a => sepRun us (patIdx l) ((a : ℕ) + 1) ++ xs a)
    (fun l => sepRun us (patIdx l) (k + 1)) none

/-- The word that remains to be written after the letter `l`. -/
def patTarget (us xs : ℕ → List B) (k : ℕ) : Option (Fin k) → (ℕ → ℕ) → List B
  | none, c => patTail us xs k 0 c
  | some b, c => RegGrowth.loopPow (xs b) (c (b : ℕ)) ++ patTail us xs k ((b : ℕ) + 1) c

lemma patEmit_aux (us xs : ℕ → List B) (k : ℕ) :
    ∀ (v : List (Fin k)) (l : Option (Fin k)), SortedFrom l v →
      seqFinEval (fun (_ : Option (Fin k)) (a : Fin k) => (some a : Option (Fin k)))
        (fun l a => sepRun us (patIdx l) ((a : ℕ) + 1) ++ xs a)
        (fun l => sepRun us (patIdx l) (k + 1)) l v
      = patTarget us xs k l (cnt v) := by
  intro v
  induction v with
  | nil =>
      intro l _
      rw [seqFinEval_nil]
      cases l with
      | none =>
          rw [patTarget, patTail_zero us xs (Nat.zero_le _) _ (fun t _ _ => cnt_nil t)]
          rfl
      | some b =>
          have hb : (b : ℕ) + 1 ≤ k := b.isLt
          rw [patTarget, patTail_zero us xs hb _ (fun t _ _ => cnt_nil t)]
          simp [patIdx]
  | cons a v ih =>
      intro l hl
      rw [sortedFrom_cons] at hl
      obtain ⟨hla, hv⟩ := hl
      rw [seqFinEval_cons, ih (some a) hv]
      have hak : (a : ℕ) < k := a.isLt
      -- the letters of `a :: v` are all at least `a`
      have hge : ∀ b ∈ a :: v, (a : ℕ) ≤ (b : ℕ) := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact le_rfl
        · exact hv.2 a rfl b hb'
      have hzero : ∀ t, t < (a : ℕ) → cnt (a :: v) t = 0 := by
        intro t ht
        refine cnt_eq_zero fun b hb => ?_
        have := hge b hb
        omega
      have hcntv : cnt (a :: v) (a : ℕ) = cnt v (a : ℕ) + 1 := cnt_cons_self a v
      have hcong : patTail us xs k ((a : ℕ) + 1) (cnt v)
          = patTail us xs k ((a : ℕ) + 1) (cnt (a :: v)) := by
        refine patTail_congr us xs k k _ (by omega) _ _ (fun t ht _ => ?_)
        exact (cnt_cons_of_ne (by omega) v).symm
      have hstep : patTail us xs k (a : ℕ) (cnt (a :: v))
          = us (a : ℕ) ++ RegGrowth.loopPow (xs (a : ℕ)) (cnt (a :: v) (a : ℕ))
              ++ patTail us xs k ((a : ℕ) + 1) (cnt (a :: v)) :=
        patTail_lt us xs hak _
      have hloop : xs (a : ℕ) ++ RegGrowth.loopPow (xs (a : ℕ)) (cnt v (a : ℕ))
          = RegGrowth.loopPow (xs (a : ℕ)) (cnt (a :: v) (a : ℕ)) := by
        rw [hcntv, RegGrowth.loopPow_succ]
      cases l with
      | none =>
          rw [patTarget, patTail_skip us xs k (cnt (a :: v)) (Nat.zero_le _) (by omega)
            (fun t _ ht => hzero t ht), hstep, patTarget]
          rw [show (patIdx (none : Option (Fin k))) = 0 from rfl, ← hcong, ← hloop,
            sepRun_succ_right us (Nat.zero_le _)]
          simp [List.append_assoc]
      | some b =>
          have hba : (b : ℕ) ≤ (a : ℕ) := hla b rfl
          rw [patTarget, patTarget]
          rcases eq_or_lt_of_le hba with heq | hlt
          · rw [show (patIdx (some b)) = (b : ℕ) + 1 from rfl, heq,
              sepRun_self, ← hcong, ← hloop]
            simp [List.append_assoc]
          · have hzero' : cnt (a :: v) (b : ℕ) = 0 := hzero _ hlt
            rw [hzero', RegGrowth.loopPow_zero, List.nil_append,
              patTail_skip us xs k (cnt (a :: v)) (by omega) (by omega)
                (fun t _ ht => hzero t ht), hstep,
              show (patIdx (some b)) = (b : ℕ) + 1 from rfl, ← hcong, ← hloop,
              sepRun_succ_right us (by omega)]
            simp [List.append_assoc]

/-- **The pattern emitter is correct on the sorted words.** -/
theorem patEmit_sorted (us xs : ℕ → List B) (k : ℕ) {v : List (Fin k)}
    (hv : v.Pairwise (· ≤ ·)) : patEmit us xs k v = chainWord us xs k (cnt v) := by
  rw [patEmit, patEmit_aux us xs k v none ⟨hv, fun b hb => absurd hb (by simp)⟩, patTarget,
    chainWord_eq_patTail]

/-- **The pattern emitter is rational.** -/
theorem isRationalFun_patEmit [Finite B] (us xs : ℕ → List B) (k : ℕ) :
    IsRationalFun (patEmit us xs k) :=
  isRationalFun_seqFinEval _ _ _ _

/-- **The pattern emitter is injective on the sorted words**, as soon as the words of the pattern
determine the numbers of times its loops are taken. -/
theorem patEmit_injOn_sorted (us xs : ℕ → List B) (k : ℕ)
    (hinj : ∀ c c' : ℕ → ℕ, chainWord us xs k c = chainWord us xs k c' → ∀ i, i < k → c i = c' i)
    {v v' : List (Fin k)} (hv : v.Pairwise (· ≤ ·)) (hv' : v'.Pairwise (· ≤ ·))
    (h : patEmit us xs k v = patEmit us xs k v') : v = v' := by
  rw [patEmit_sorted us xs k hv, patEmit_sorted us xs k hv'] at h
  refine sorted_eq_of_cnt hv hv' fun i => ?_
  by_cases hik : i < k
  · exact hinj _ _ h i hik
  · rw [cnt_eq_zero_of_le v (by omega), cnt_eq_zero_of_le v' (by omega)]

end Pattern

end Transducers.Exercises
