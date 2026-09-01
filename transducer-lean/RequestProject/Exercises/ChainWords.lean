/-
The words produced by a chain of loops in a deterministic automaton: the `k`-pattern that a
regular language of growth `Ω(n^k)` contains, and its transport to the range of a rational
function.
-/
import RequestProject.Exercises.RationalGrowth

/-!
# The `k`-pattern of a language of growth `Ω(n^k)`

The loop analysis of `RequestProject/Exercises/RegularGrowth.lean` shows that a nonempty regular
language `L` either has two loops with different labels of the same length — and then its growth
is super-polynomial — or its growth is `Θ(n^k)`, where `k` is the length of the longest *chain of
loops* (`Transducers.Exercises.RegGrowth.Chain`) in a deterministic automaton for `L`.  This file
extracts from a chain of `k` loops the family of words it produces:

* `Transducers.Exercises.chainWord us xs k c` is the word
  `us 0 · (xs 0)^(c 0) · us 1 · (xs 1)^(c 1) ⋯ (xs (k-1))^(c (k-1)) · us k`;
* `Transducers.Exercises.RegGrowth.chain_words` — a chain of `k` loops from `q` gives words
  `us` and loops `xs` such that every `chainWord us xs k c` is accepted from `q`, and the word
  determines the `k` exponents;
* `Transducers.Exercises.regular_chain_words` — a regular language of growth `Ω(n^k)` either has
  two loops, or contains such a `k`-pattern;
* `Transducers.Exercises.rationalFun_chain_words` — the same for the range of a rational function
  with `Ω(n^k)` outputs, where the case of two loops is replaced by its consequence, the identity
  of `{0,1}*` among the rational pre- and post-compositions of the function.

This is the `k`-pattern that the author's solution to Exercise `exer:polynomial-ideals` uses.
-/

namespace Transducers.Exercises

open scoped Classical

open Transducers

/-! ### The words of a chain of loops -/

/-- The word `us 0 · (xs 0)^(c 0) · us 1 · (xs 1)^(c 1) ⋯ (xs (k-1))^(c (k-1)) · us k`: the shape
of the words produced by a chain of `k` loops. -/
def chainWord {A : Type} (us xs : ℕ → List A) : ℕ → (ℕ → ℕ) → List A
  | 0, _ => us 0
  | (k + 1), c =>
      us 0 ++ RegGrowth.loopPow (xs 0) (c 0) ++
        chainWord (fun i => us (i + 1)) (fun i => xs (i + 1)) k (fun i => c (i + 1))

@[simp] lemma chainWord_zero {A : Type} (us xs : ℕ → List A) (c : ℕ → ℕ) :
    chainWord us xs 0 c = us 0 := rfl

lemma chainWord_succ {A : Type} (us xs : ℕ → List A) (k : ℕ) (c : ℕ → ℕ) :
    chainWord us xs (k + 1) c =
      us 0 ++ RegGrowth.loopPow (xs 0) (c 0) ++
        chainWord (fun i => us (i + 1)) (fun i => xs (i + 1)) k (fun i => c (i + 1)) := rfl

/-- Prefixing the first separator of a chain word prefixes the whole word. -/
lemma chainWord_prepend {A : Type} (u : List A) (us xs : ℕ → List A) (k : ℕ) (c : ℕ → ℕ) :
    chainWord (fun i => if i = 0 then u ++ us 0 else us i) xs k c
      = u ++ chainWord us xs k c := by
  cases k with
  | zero => simp
  | succ k =>
      rw [chainWord_succ, chainWord_succ]
      simp [List.append_assoc]

/-- **The words of a chain of loops.**  A chain of `k` loops from `q` produces a family of words
accepted from `q`, indexed by the `k` numbers of times the loops are taken, and the word
determines those `k` numbers. -/
theorem RegGrowth.chain_words {A σ : Type} {M : DFA A σ} {q : σ} {k : ℕ}
    (h : RegGrowth.Chain M q k) :
    ∃ us xs : ℕ → List A, (∀ i, i < k → xs i ≠ []) ∧
      (∀ c : ℕ → ℕ, M.evalFrom q (chainWord us xs k c) ∈ M.accept) ∧
      (∀ c c' : ℕ → ℕ, chainWord us xs k c = chainWord us xs k c' → ∀ i, i < k → c i = c' i) := by
  induction k generalizing q with
  | zero =>
      obtain ⟨w, hw⟩ := h
      exact ⟨fun _ => w, fun _ => [], fun i hi => absurd hi (Nat.not_lt_zero i),
        fun _ => hw, fun _ _ _ i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ k ih =>
      obtain ⟨r, ⟨u₀, hu₀⟩, ⟨x, hxne, hx⟩, hrest⟩ := h
      have hxpos : 0 < x.length := List.length_pos_iff.mpr hxne
      rcases hrest with ⟨rfl, ⟨u, hu⟩⟩ | ⟨r', ⟨u, hu⟩, hnot, hc⟩
      · refine ⟨fun i => if i = 0 then u₀ else u, fun _ => x, ?_, ?_, ?_⟩
        · intro i _
          exact hxne
        · intro c
          have hval : chainWord (fun i => if i = 0 then u₀ else u) (fun _ => x) 1 c
              = u₀ ++ RegGrowth.loopPow x (c 0) ++ u := by
            rw [chainWord_succ]
            simp
          rw [hval, M.evalFrom_of_append, M.evalFrom_of_append, hu₀,
            RegGrowth.evalFrom_loopPow hx]
          exact hu
        · intro c c' heq i hi
          have hval : ∀ d : ℕ → ℕ, chainWord (fun i => if i = 0 then u₀ else u) (fun _ => x) 1 d
              = u₀ ++ RegGrowth.loopPow x (d 0) ++ u := by
            intro d
            rw [chainWord_succ]
            simp
          rw [hval c, hval c'] at heq
          have hlen := congrArg List.length heq
          simp only [List.length_append, RegGrowth.loopPow_length] at hlen
          have h0 : c 0 = c' 0 := Nat.eq_of_mul_eq_mul_right hxpos (by omega)
          interval_cases i
          · exact h0
      · obtain ⟨us', xs', hxs', hacc', hinj'⟩ := ih hc
        refine ⟨fun i => if i = 0 then u₀ else if i = 1 then u ++ us' 0 else us' (i - 1),
          fun i => if i = 0 then x else xs' (i - 1), ?_, ?_, ?_⟩
        · intro i hi
          cases i with
          | zero => simpa using hxne
          | succ j =>
              simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
              exact hxs' j (by omega)
        all_goals
          have key : ∀ d : ℕ → ℕ,
              chainWord (fun i => if i = 0 then u₀ else if i = 1 then u ++ us' 0 else us' (i - 1))
                  (fun i => if i = 0 then x else xs' (i - 1)) (k + 1) d
                = u₀ ++ RegGrowth.loopPow x (d 0) ++ (u ++ chainWord us' xs' k
                    (fun i => d (i + 1))) := by
            intro d
            rw [chainWord_succ]
            have h1 : (fun i => if i + 1 = 0 then u₀ else
                if i + 1 = 1 then u ++ us' 0 else us' (i + 1 - 1))
                = fun i => if i = 0 then u ++ us' 0 else us' i := by
              funext i
              cases i with
              | zero => simp
              | succ j => simp
            have h2 : (fun i => if i + 1 = 0 then x else xs' (i + 1 - 1)) = xs' := by
              funext i
              simp
            rw [h1, h2, chainWord_prepend]
            simp
        · intro c
          rw [key c]
          simp only [← List.append_assoc]
          rw [M.evalFrom_of_append, M.evalFrom_of_append, M.evalFrom_of_append, hu₀,
            RegGrowth.evalFrom_loopPow hx, hu]
          exact hacc' _
        · intro c c' heq i hi
          rw [key c, key c'] at heq
          simp only [← List.append_assoc] at heq
          obtain ⟨h0, hrest⟩ := RegGrowth.loop_words_inj hx hxne hu hnot heq
          cases i with
          | zero => exact h0
          | succ j => exact hinj' _ _ hrest j (by omega)

/-! ### The `k`-pattern of a regular language of growth `Ω(n^k)` -/

/-- The number of words of length at most `n` grows with `n`. -/
lemma langCount_mono {A : Type} [Finite A] {L : Language A} {m n : ℕ} (h : m ≤ n) :
    langCount L m ≤ langCount L n := by
  refine Set.ncard_le_ncard (fun w hw => ⟨hw.1, le_trans hw.2 h⟩) ?_
  exact (finite_lists_length_le n).subset (fun v hv => hv.2)

/-- **A regular language of growth `Ω(n^k)` contains a `k`-pattern.**  Unless the language has two
loops of the same length with different labels — in which case its growth is super-polynomial —
it contains the words of a chain of `k` loops. -/
theorem regular_chain_words {A : Type} [Finite A] {L : Language A} (hL : L.IsRegular)
    (hne : ∃ w, w ∈ L) {k c₀ N₀ : ℕ}
    (hΩ : ∀ n, N₀ ≤ n → (n + 1) ^ k ≤ c₀ * langCount L n) :
    (∃ p x y s : List A, 0 < x.length ∧ x.length = y.length ∧ x ≠ y ∧
        ∀ u : List Bool, p ++ cycleWord x y u ++ s ∈ L) ∨
      (∃ us xs : ℕ → List A, (∀ i, i < k → xs i ≠ []) ∧
        (∀ c : ℕ → ℕ, chainWord us xs k c ∈ L) ∧
        (∀ c c' : ℕ → ℕ, chainWord us xs k c = chainWord us xs k c' →
          ∀ i, i < k → c i = c' i)) := by
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
    have hcyc : M.evalFrom q (cycleWord x y u) = q := by
      induction u with
      | nil => rfl
      | cons b u ih =>
          cases b
          · rw [cycleWord_cons_false, M.evalFrom_of_append, hy, ih]
          · rw [cycleWord_cons_true, M.evalFrom_of_append, hx, ih]
    show M.evalFrom M.start (pw ++ cycleWord x y u ++ sw) ∈ M.accept
    rw [M.evalFrom_of_append, M.evalFrom_of_append, hp, hcyc]
    exact hs
  · right
    have hchain : RegGrowth.Chain M M.start k := by
      cases k with
      | zero =>
          obtain ⟨w, hw⟩ := hne
          exact ⟨w, hw⟩
      | succ j =>
          by_contra hnot
          obtain ⟨C, hC⟩ := RegGrowth.accCount_le_of_not_chain hamb (Fintype.card σ) M.start j
            (Finset.card_le_univ _) (RegGrowth.reaches_refl _) hnot
          set n := max N₀ (c₀ * C) with hn
          have h1 : (n + 1) ^ (j + 1) ≤ c₀ * langCount M.accepts n := hΩ n (le_max_left _ _)
          have h2 : langCount M.accepts n ≤ C * (n + 1) ^ j := by
            rw [hcount]; exact hC n
          have h3 : (n + 1) ^ (j + 1) ≤ c₀ * (C * (n + 1) ^ j) :=
            le_trans h1 (Nat.mul_le_mul_left _ h2)
          have h4 : (n + 1) * (n + 1) ^ j ≤ (c₀ * C) * (n + 1) ^ j := by
            calc (n + 1) * (n + 1) ^ j = (n + 1) ^ (j + 1) := by ring
              _ ≤ c₀ * (C * (n + 1) ^ j) := h3
              _ = (c₀ * C) * (n + 1) ^ j := by ring
          have hpos : 0 < (n + 1) ^ j := Nat.pow_pos (Nat.succ_pos n)
          have h5 : n + 1 ≤ c₀ * C := Nat.le_of_mul_le_mul_right h4 hpos
          have h6 : c₀ * C ≤ n := le_max_right _ _
          omega
    obtain ⟨us, xs, hxs, hacc, hinj⟩ := RegGrowth.chain_words hchain
    exact ⟨us, xs, hxs, fun c => hacc c, hinj⟩

/-! ### The `k`-pattern in the range of a rational function -/

/-- The growth of the range of a rational function is at least the growth of the number of its
outputs, up to a polynomial change of the scale. -/
lemma langCount_range_omega {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) {k c N : ℕ} (hc : 0 < c)
    (hΩ : ∀ n, N ≤ n → (n + 1) ^ k ≤ c * (f '' {w : List A | w.length ≤ n}).ncard) :
    ∃ c' : ℕ, 0 < c' ∧ ∃ N' : ℕ, ∀ m, N' ≤ m →
      (m + 1) ^ k ≤ c' * langCount ({v | ∃ w, v = f w} : Language B) m := by
  classical
  obtain ⟨C0, hC0⟩ := exists_output_length_bound hf
  set C1 := C0 + 1 with hC1
  have hC1pos : 0 < C1 := by omega
  refine ⟨c * (2 * C1) ^ k, Nat.mul_pos hc (Nat.pow_pos (by omega)),
    max (2 * C1) (C1 * (N + 1)), fun m hm => ?_⟩
  have hm2 : C1 * (N + 1) ≤ m := le_trans (le_max_right _ _) hm
  set t := m / C1 with ht
  have hdm : C1 * t + m % C1 = m := Nat.div_add_mod m C1
  have hmod : m % C1 < C1 := Nat.mod_lt _ hC1pos
  have htN : N + 1 ≤ t := by
    rw [ht]
    exact (Nat.le_div_iff_mul_le hC1pos).mpr (by rw [Nat.mul_comm]; exact hm2)
  have htpos : 1 ≤ t := by omega
  have hC1t : C1 ≤ C1 * t := Nat.le_mul_of_pos_right _ (by omega)
  have h2t : 2 * C1 * t = C1 * t + C1 * t := by ring
  have htle : C1 * t ≤ m := by omega
  have hmt : m + 1 ≤ 2 * C1 * t := by omega
  obtain ⟨n, hn⟩ : ∃ n, n + 1 = t := ⟨t - 1, by omega⟩
  have hnN : N ≤ n := by omega
  have hstep : (n + 1) ^ k ≤ c * (f '' {w : List A | w.length ≤ n}).ncard := hΩ n hnN
  have hstep2 : (f '' {w : List A | w.length ≤ n}).ncard
      ≤ langCount ({v | ∃ w, v = f w} : Language B) (C0 * (n + 1)) :=
    outSet_ncard_le_langCount hC0 n
  have hCle : C0 * (n + 1) ≤ C1 * t := by
    rw [hn]
    exact Nat.mul_le_mul_right _ (by omega)
  have hle : C0 * (n + 1) ≤ m := by omega
  have hstep3 : langCount ({v | ∃ w, v = f w} : Language B) (C0 * (n + 1))
      ≤ langCount ({v | ∃ w, v = f w} : Language B) m := langCount_mono hle
  calc (m + 1) ^ k ≤ (2 * C1 * t) ^ k := Nat.pow_le_pow_left hmt k
    _ = (2 * C1) ^ k * (n + 1) ^ k := by rw [← hn, mul_pow]
    _ ≤ (2 * C1) ^ k * (c * (f '' {w : List A | w.length ≤ n}).ncard) :=
        Nat.mul_le_mul_left _ hstep
    _ ≤ (2 * C1) ^ k * (c * langCount ({v | ∃ w, v = f w} : Language B) m) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_trans hstep2 hstep3))
    _ = c * (2 * C1) ^ k * langCount ({v | ∃ w, v = f w} : Language B) m := by ring

/-- **The `k`-pattern in the range of a rational function with `Ω(n^k)` outputs.**  Either the
identity of `{0,1}*` is a rational pre- and post-composition of `f` — the case of two loops, which
by Exercise `exer:full-ideal` puts every rational function among them — or the range of `f`
contains the words of a chain of `k` loops. -/
theorem rationalFun_chain_words {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) {k c N : ℕ} (hc : 0 < c)
    (hΩ : ∀ n, N ≤ n → (n + 1) ^ k ≤ c * (f '' {w : List A | w.length ≤ n}).ncard) :
    (∃ (g : List Bool → List A) (h : List B → List Bool),
        IsRationalFun g ∧ IsRationalFun h ∧ ∀ u : List Bool, h (f (g u)) = u) ∨
      (∃ us xs : ℕ → List B, (∀ i, i < k → xs i ≠ []) ∧
        (∀ c : ℕ → ℕ, ∃ w : List A, f w = chainWord us xs k c) ∧
        (∀ c c' : ℕ → ℕ, chainWord us xs k c = chainWord us xs k c' →
          ∀ i, i < k → c i = c' i)) := by
  classical
  have hLreg : Language.IsRegular ({v | ∃ w, v = f w} : Language B) :=
    rationalRel_range_isRegular hf
  have hnel : ∃ v, v ∈ ({v | ∃ w, v = f w} : Language B) := ⟨f [], [], rfl⟩
  obtain ⟨c', -, N', hΩ'⟩ := langCount_range_omega hf hc hΩ
  rcases regular_chain_words hLreg hnel hΩ' with
    ⟨p, x, y, s, hxpos, hlen, hxy, hmem⟩ | ⟨us, xs, hxs, hmem, hinj⟩
  · exact Or.inl (exists_rational_bool_identity_of_range_loops hf hxpos hlen hxy
      (fun u => (hmem u).imp fun _ h => h.symm))
  · exact Or.inr ⟨us, xs, hxs, fun d => (hmem d).imp fun _ h => h.symm, hinj⟩

end Transducers.Exercises
