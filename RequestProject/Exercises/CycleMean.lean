/-
The maximum cycle mean of a transducer: the maximal output length of a rational function on the
inputs of length at most `n` is `(p/q)·n` up to an additive constant.

This is the analysis that the solutions of the exercises on functions of exactly linear output
size (`RequestProject/Exercises/LinearOutput.lean`) rest on, and that the author of *Transducers*
(M. Bojańczyk) carries out only in outline.  It is a weighted refinement of the loop analysis of
`RequestProject/PartB/PathComb.lean`: weight every transition of an nfa with output by the length
of the string that it reads and by the length of the string that it writes, and compare the two
weights along the cycles of the automaton.
-/
import RequestProject.PartB.PathComb
import RequestProject.PartB.LenNormalForm

/-!
# The maximum cycle mean of an nfa with output

Let `M` be an nfa with output computing a *function* `f`, and let `p/q` be the largest ratio
(length of the output)/(length of the input) of a cycle of `M` through a productive state, taken
over the cycles that use at most `|Q|` transitions — a maximum over a finite set of pairs of
natural numbers, so `p` and `q` are the numerator and the denominator of a rational number.

* `Transducers.Exercises.CycleMean.cycle_bound` — *every* cycle through a productive state, not
  only the short ones, has `q·(output) ≤ p·(input)`.  A long cycle is split into a short cycle and
  a shorter cycle by the pigeonhole principle of
  `Transducers.LabAut.Path.small_loop`, and the two bounds are added.
* `Transducers.Exercises.CycleMean.path_bound` — every path between a reachable state and a
  co-reachable state has `q·(output) ≤ p·(input) + q·K`, where `K` is the largest output length of
  a path with at most `|Q|` transitions: the cycles of the path are removed one at a time.
* `Transducers.Exercises.CycleMean.exists_linear_rate` — the resulting two-sided bound on the
  output lengths of `f`.  The lower bound comes from iterating a cycle that attains the maximum:
  such a cycle passes through a productive state, so it can be preceded by a path from an initial
  state and followed by a path to a final state, and this is where the maximum being attained (and
  not only approached) is used.

The one place where `f` being a function, and not merely a rational relation, is used is
`Transducers.Exercises.CycleMean.outputOf_eq_nil_of_cycle_of_input_nil`: a cycle through a
productive state that reads nothing writes nothing, since otherwise one input would have two
outputs.  Without it a cycle reading nothing and writing something would make the mean infinite.
-/

namespace Transducers.Exercises

namespace CycleMean

open LabAut NFAO

variable {A B Q : Type} {M : NFAO A B Q}

/-! ### Elementary bounds along a path -/

/-- The output of a path is at most the number of its transitions times the largest output of a
transition. -/
lemma outputOf_length_le_of_path {Bmax : ℕ} (hB : ∀ t ∈ M.δ, (t.2.2.1 : List B).length ≤ Bmax) :
    ∀ {x y : Q} {ts : List (Q × List A × List B × Q)}, M.Path x ts y →
      (NFAO.outputOf ts).length ≤ Bmax * ts.length := by
  intro x y ts h
  induction h with
  | nil q => simp
  | @cons q u l q' ts p ht _ ih =>
      have h1 : l.length ≤ Bmax := hB _ ht
      have h2 : l.length + (NFAO.outputOf ts).length ≤ Bmax + Bmax * ts.length :=
        Nat.add_le_add h1 ih
      have h3 : Bmax * (ts.length + 1) = Bmax * ts.length + Bmax := by ring
      simpa [NFAO.outputOf_cons, h3] using by linarith [h2]

/-- The input of a path is at most the number of its transitions times the largest input of a
transition. -/
lemma inputOf_length_le_of_path {Amax : ℕ} (hA : ∀ t ∈ M.δ, (t.2.1 : List A).length ≤ Amax) :
    ∀ {x y : Q} {ts : List (Q × List A × List B × Q)}, M.Path x ts y →
      (LabAut.inputOf ts).length ≤ Amax * ts.length := by
  intro x y ts h
  induction h with
  | nil q => simp
  | @cons q u l q' ts p ht _ ih =>
      have h1 : u.length ≤ Amax := hA _ ht
      have h2 : u.length + (LabAut.inputOf ts).length ≤ Amax + Amax * ts.length :=
        Nat.add_le_add h1 ih
      have h3 : Amax * (ts.length + 1) = Amax * ts.length + Amax := by ring
      simpa [LabAut.inputOf_cons, h3] using by linarith [h2]

/-! ### Reachability -/

/-- Reachability is preserved along a path. -/
lemma reach_of_path {x r : Q} {ts : List (Q × List A × List B × Q)}
    (hx : LenNF.Reach M x) (h : M.Path x ts r) : LenNF.Reach M r := by
  obtain ⟨q₀, h₀, tsa, hpa⟩ := hx
  exact ⟨q₀, h₀, tsa ++ ts, hpa.append h⟩

/-- Co-reachability is preserved backwards along a path. -/
lemma coReach_of_path {r y : Q} {ts : List (Q × List A × List B × Q)}
    (hy : LenNF.CoReach M y) (h : M.Path r ts y) : LenNF.CoReach M r := by
  obtain ⟨pf, hpf, tsb, hpb⟩ := hy
  exact ⟨pf, hpf, ts ++ tsb, h.append hpb⟩

/-! ### A cycle that reads nothing writes nothing -/

/-- If the automaton computes a *function*, then a cycle through a productive state whose input is
empty has an empty output: otherwise the same input string would have two different outputs. -/
lemma outputOf_eq_nil_of_cycle_of_input_nil {f : List A → List B}
    (hM : ∀ w v, M.rel w v ↔ v = f w) {s : Q} {ts : List (Q × List A × List B × Q)}
    (hs : Productive M s) (hc : M.Path s ts s) (hin : LabAut.inputOf ts = []) :
    NFAO.outputOf ts = [] := by
  obtain ⟨q₀, h₀, pf, hpf, ts₁, ts₂, h1, h2⟩ := hs
  have hr1 : M.rel (LabAut.inputOf (ts₁ ++ ts₂)) (NFAO.outputOf (ts₁ ++ ts₂)) :=
    ⟨_, ⟨q₀, h₀, pf, hpf, h1.append h2⟩, rfl, rfl⟩
  have hr2 : M.rel (LabAut.inputOf (ts₁ ++ ts ++ ts₂)) (NFAO.outputOf (ts₁ ++ ts ++ ts₂)) :=
    ⟨_, ⟨q₀, h₀, pf, hpf, (h1.append hc).append h2⟩, rfl, rfl⟩
  rw [hM] at hr1 hr2
  have hinEq : LabAut.inputOf (ts₁ ++ ts ++ ts₂) = LabAut.inputOf (ts₁ ++ ts₂) := by
    simp [LabAut.inputOf_append, hin]
  rw [hinEq, ← hr1] at hr2
  have hlen := congrArg List.length hr2
  simp only [NFAO.outputOf_append, List.length_append] at hlen
  exact List.length_eq_zero_iff.1 (by omega)

/-! ### The bound along an arbitrary cycle -/

/-- If every cycle through a productive state that uses at most `|S|` transitions has mean at most
`pn/qd`, then so does every cycle through a productive state.  A long cycle is split by the
pigeonhole principle into a short cycle and a strictly shorter cycle. -/
lemma cycle_bound {S : List Q} (hS : ∀ x : Q, x ∈ S) {pn qd : ℕ}
    (hshort : ∀ (s : Q) (ts : List (Q × List A × List B × Q)), Productive M s → M.Path s ts s →
      ts.length ≤ S.length →
      qd * (NFAO.outputOf ts).length ≤ pn * (LabAut.inputOf ts).length) :
    ∀ {s : Q} {ts : List (Q × List A × List B × Q)}, Productive M s → M.Path s ts s →
      qd * (NFAO.outputOf ts).length ≤ pn * (LabAut.inputOf ts).length := by
  intro s ts
  generalize hn : ts.length = n
  induction n using Nat.strong_induction_on generalizing s ts with
  | _ n ih =>
    intro hs hc
    by_cases hlen : ts.length ≤ S.length
    · exact hshort s ts hs hc hlen
    · push_neg at hlen
      obtain ⟨ts₁, ts₂, ts₃, r, rfl, hne, hlen2, h1, h2, h3⟩ :=
        LabAut.Path.small_loop S (fun t _ => hS _) hc (hS s) hlen.le
      have hsr : LenNF.Reach M s := ((LenNF.productive_iff M s).1 hs).1
      have hsc : LenNF.CoReach M s := ((LenNF.productive_iff M s).1 hs).2
      have hr : Productive M r :=
        (LenNF.productive_iff M r).2 ⟨reach_of_path hsr h1, coReach_of_path hsc h3⟩
      have hb2 := hshort r ts₂ hr h2 hlen2
      have hne' : 0 < ts₂.length := List.length_pos_iff.2 hne
      have hlt : (ts₁ ++ ts₃).length < n := by
        subst hn; simp only [List.length_append]; omega
      have hb13 := ih _ hlt rfl hs (h1.append h3)
      simp only [NFAO.outputOf_append, LabAut.inputOf_append, List.length_append] at hb13 ⊢
      have e1 : qd * ((NFAO.outputOf ts₁).length + (NFAO.outputOf ts₂).length +
          (NFAO.outputOf ts₃).length)
          = qd * ((NFAO.outputOf ts₁).length + (NFAO.outputOf ts₃).length) +
            qd * (NFAO.outputOf ts₂).length := by ring
      have e2 : pn * ((LabAut.inputOf ts₁).length + (LabAut.inputOf ts₂).length +
          (LabAut.inputOf ts₃).length)
          = pn * ((LabAut.inputOf ts₁).length + (LabAut.inputOf ts₃).length) +
            pn * (LabAut.inputOf ts₂).length := by ring
      rw [e1, e2]
      exact Nat.add_le_add hb13 hb2

/-! ### The bound along an arbitrary path -/

/-- Every path between a reachable state and a co-reachable state has
`qd·(output) ≤ pn·(input) + qd·K`, where `K = Bmax·|S|` bounds the output of a path that uses at
most `|S|` transitions.  The cycles of the path are removed one at a time. -/
lemma path_bound {S : List Q} (hS : ∀ x : Q, x ∈ S) {pn qd Bmax : ℕ}
    (hB : ∀ t ∈ M.δ, (t.2.2.1 : List B).length ≤ Bmax)
    (hcyc : ∀ (s : Q) (ts : List (Q × List A × List B × Q)), Productive M s → M.Path s ts s →
      qd * (NFAO.outputOf ts).length ≤ pn * (LabAut.inputOf ts).length) :
    ∀ {x y : Q} {ts : List (Q × List A × List B × Q)}, LenNF.Reach M x → LenNF.CoReach M y →
      M.Path x ts y →
      qd * (NFAO.outputOf ts).length ≤ pn * (LabAut.inputOf ts).length + qd * (Bmax * S.length) := by
  intro x y ts
  generalize hn : ts.length = n
  induction n using Nat.strong_induction_on generalizing x y ts with
  | _ n ih =>
    intro hx hy h
    by_cases hlen : ts.length ≤ S.length
    · have h1 : (NFAO.outputOf ts).length ≤ Bmax * S.length :=
        le_trans (outputOf_length_le_of_path hB h) (Nat.mul_le_mul_left _ hlen)
      have := Nat.mul_le_mul_left qd h1
      omega
    · push_neg at hlen
      obtain ⟨ts₁, ts₂, ts₃, r, rfl, hne, hlen2, h1, h2, h3⟩ :=
        LabAut.Path.small_loop S (fun t _ => hS _) h (hS x) hlen.le
      have hr : Productive M r :=
        (LenNF.productive_iff M r).2
          ⟨reach_of_path hx h1, coReach_of_path hy (h2.append h3)⟩
      have hb2 := hcyc r ts₂ hr h2
      have hne' : 0 < ts₂.length := List.length_pos_iff.2 hne
      have hlt : (ts₁ ++ ts₃).length < n := by
        subst hn; simp only [List.length_append]; omega
      have hb13 := ih _ hlt rfl hx hy (h1.append h3)
      simp only [NFAO.outputOf_append, LabAut.inputOf_append, List.length_append] at hb13 ⊢
      have e1 : qd * ((NFAO.outputOf ts₁).length + (NFAO.outputOf ts₂).length +
          (NFAO.outputOf ts₃).length)
          = qd * ((NFAO.outputOf ts₁).length + (NFAO.outputOf ts₃).length) +
            qd * (NFAO.outputOf ts₂).length := by ring
      have e2 : pn * ((LabAut.inputOf ts₁).length + (LabAut.inputOf ts₂).length +
          (LabAut.inputOf ts₃).length)
          = pn * ((LabAut.inputOf ts₁).length + (LabAut.inputOf ts₃).length) +
            pn * (LabAut.inputOf ts₂).length := by ring
      rw [e1, e2]
      omega

/-! ### Iterating a cycle -/

/-- The concatenation of `k` copies of a list. -/
def catPow {α : Type} (l : List α) (k : ℕ) : List α := (List.replicate k l).flatten

@[simp] lemma catPow_zero {α : Type} (l : List α) : catPow l 0 = [] := by simp [catPow]

lemma catPow_succ {α : Type} (l : List α) (k : ℕ) : catPow l (k + 1) = l ++ catPow l k := by
  simp [catPow, List.replicate_succ]

lemma path_catPow {s : Q} {ts : List (Q × List A × List B × Q)} (h : M.Path s ts s) :
    ∀ k : ℕ, M.Path s (catPow ts k) s := by
  intro k
  induction k with
  | zero => simpa using LabAut.Path.nil s
  | succ k ihk => rw [catPow_succ]; exact h.append ihk

lemma inputOf_catPow (ts : List (Q × List A × List B × Q)) (k : ℕ) :
    (LabAut.inputOf (catPow ts k)).length = k * (LabAut.inputOf ts).length := by
  induction k with
  | zero => simp
  | succ k ihk =>
      rw [catPow_succ, LabAut.inputOf_append, List.length_append, ihk]
      ring

lemma outputOf_catPow (ts : List (Q × List A × List B × Q)) (k : ℕ) :
    (NFAO.outputOf (catPow ts k)).length = k * (NFAO.outputOf ts).length := by
  induction k with
  | zero => simp
  | succ k ihk =>
      rw [catPow_succ, NFAO.outputOf_append, List.length_append, ihk]
      ring

/-! ### The rate of a rational function -/

/-- **The maximum cycle mean.**  For a rational function `f` there are natural numbers `pn`, `qd`
with `qd > 0` and a constant `C` such that

* every input `w` of length at most `n` has `qd·|f w| ≤ pn·n + C`, and
* some input `w` of length at most `n` has `pn·n ≤ qd·|f w| + C`.

The pair `pn/qd` is the largest ratio (output length)/(input length) of a cycle of a transducer
for `f` through a productive state. -/
theorem exists_linear_rate {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) :
    ∃ pn qd C : ℕ, 0 < qd ∧ ∀ n : ℕ,
      (∀ w : List A, w.length ≤ n → qd * (f w).length ≤ pn * n + C) ∧
      (∃ w : List A, w.length ≤ n ∧ pn * n ≤ qd * (f w).length + C) := by
  classical
  obtain ⟨Q, hQfin, M, hMrel⟩ := hf
  have hM : ∀ w v, M.rel w v ↔ v = f w := fun w v => (hMrel w v).symm
  -- a list of all the states
  obtain ⟨S, hS⟩ : ∃ S : List Q, ∀ x : Q, x ∈ S := by
    letI := Fintype.ofFinite Q
    exact ⟨Finset.univ.toList, by simp⟩
  -- bounds on the labels of a transition
  obtain ⟨Bmax, hB⟩ : ∃ Bmax : ℕ, ∀ t ∈ M.δ, (t.2.2.1 : List B).length ≤ Bmax := by
    obtain ⟨Bmax, hBmax⟩ := (M.δ_finite.image (fun t => (t.2.2.1 : List B).length)).bddAbove
    exact ⟨Bmax, fun t ht => hBmax ⟨t, ht, rfl⟩⟩
  obtain ⟨Amax, hA⟩ : ∃ Amax : ℕ, ∀ t ∈ M.δ, (t.2.1 : List A).length ≤ Amax := by
    obtain ⟨Amax, hAmax⟩ := (M.δ_finite.image (fun t => (t.2.1 : List A).length)).bddAbove
    exact ⟨Amax, fun t ht => hAmax ⟨t, ht, rfl⟩⟩
  -- the means of the short cycles through a productive state
  set CS : Set (ℕ × ℕ) := {z | 0 < z.2 ∧ ∃ (s : Q) (ts : List (Q × List A × List B × Q)),
      Productive M s ∧ M.Path s ts s ∧ ts.length ≤ S.length ∧
        (NFAO.outputOf ts).length = z.1 ∧ (LabAut.inputOf ts).length = z.2} with hCSdef
  have hCSfin : CS.Finite := by
    refine Set.Finite.subset ((Set.finite_Iic (Bmax * S.length)).prod
      (Set.finite_Iic (Amax * S.length))) ?_
    rintro z ⟨-, s, ts, -, hpath, hlen, hout, hin⟩
    constructor
    · simp only [Set.mem_Iic]
      rw [← hout]
      exact le_trans (outputOf_length_le_of_path hB hpath) (Nat.mul_le_mul_left _ hlen)
    · simp only [Set.mem_Iic]
      rw [← hin]
      exact le_trans (inputOf_length_le_of_path hA hpath) (Nat.mul_le_mul_left _ hlen)
  -- the maximum of those means, together with the trivial candidate `0/1`
  set F : Finset (ℕ × ℕ) := insert (0, 1) hCSfin.toFinset with hFdef
  obtain ⟨z, hzF, hzmax⟩ :=
    F.exists_max_image (fun z : ℕ × ℕ => (z.1 : ℚ) / z.2) ⟨(0, 1), by simp [hFdef]⟩
  obtain ⟨pn, qd⟩ := z
  have hzcases : (pn, qd) = ((0, 1) : ℕ × ℕ) ∨ (pn, qd) ∈ CS := by
    rcases Finset.mem_insert.1 hzF with h | h
    · exact Or.inl h
    · exact Or.inr (hCSfin.mem_toFinset.1 h)
  have hqpos : 0 < qd := by
    rcases hzcases with h | h
    · simp only [Prod.mk.injEq] at h; omega
    · exact h.1
  -- the maximality, as an inequality between natural numbers
  have hmax : ∀ b a : ℕ, (b, a) ∈ CS → b * qd ≤ pn * a := by
    intro b a hba
    have ha : 0 < a := hba.1
    have hmem : (b, a) ∈ F := Finset.mem_insert_of_mem (hCSfin.mem_toFinset.2 hba)
    have := hzmax (b, a) hmem
    have haQ : (0 : ℚ) < a := by exact_mod_cast ha
    have hqQ : (0 : ℚ) < qd := by exact_mod_cast hqpos
    have : (b : ℚ) * qd ≤ (pn : ℚ) * a := (div_le_div_iff₀ haQ hqQ).1 this
    exact_mod_cast this
  -- every short cycle through a productive state obeys the bound
  have hshort : ∀ (s : Q) (ts : List (Q × List A × List B × Q)), Productive M s →
      M.Path s ts s → ts.length ≤ S.length →
      qd * (NFAO.outputOf ts).length ≤ pn * (LabAut.inputOf ts).length := by
    intro s ts hs hc hlen
    rcases Nat.eq_zero_or_pos (LabAut.inputOf ts).length with h0 | h0
    · have hnil : LabAut.inputOf ts = [] := List.length_eq_zero_iff.1 h0
      rw [outputOf_eq_nil_of_cycle_of_input_nil hM hs hc hnil]
      simp
    · have : ((NFAO.outputOf ts).length, (LabAut.inputOf ts).length) ∈ CS :=
        ⟨h0, s, ts, hs, hc, hlen, rfl, rfl⟩
      have hb := hmax _ _ this
      linarith [hb]
  have hcyc : ∀ (s : Q) (ts : List (Q × List A × List B × Q)), Productive M s → M.Path s ts s →
      qd * (NFAO.outputOf ts).length ≤ pn * (LabAut.inputOf ts).length :=
    fun s ts hs hc => cycle_bound (M := M) hS hshort hs hc
  -- the upper bound
  have hupper : ∀ (w : List A), qd * (f w).length ≤ pn * w.length + qd * (Bmax * S.length) := by
    intro w
    have hrel : M.rel w (f w) := (hM w (f w)).2 rfl
    obtain ⟨ts, ⟨q₀, h₀, pf, hpf, hpath'⟩, hin, hout⟩ := hrel
    have hx : LenNF.Reach M q₀ := ⟨q₀, h₀, [], LabAut.Path.nil q₀⟩
    have hy : LenNF.CoReach M pf := ⟨pf, hpf, [], LabAut.Path.nil pf⟩
    have := path_bound (M := M) hS hB hcyc hx hy hpath'
    rw [hin, hout] at this
    exact this
  -- the lower bound, from a cycle attaining the maximum
  have hlower : ∃ C₂ : ℕ, ∀ n : ℕ, ∃ w : List A, w.length ≤ n ∧ pn * n ≤ qd * (f w).length + C₂ := by
    rcases hzcases with hz0 | hzCS
    · refine ⟨0, fun n => ⟨[], by simp, ?_⟩⟩
      simp only [Prod.mk.injEq] at hz0
      simp [hz0.1]
    · obtain ⟨-, s, c, hs, hcpath, -, hcout, hcin⟩ := hzCS
      obtain ⟨q₀, h₀, pf, hpf, tsa, tsb, hpa, hpb⟩ := hs
      set A0 := (LabAut.inputOf tsa).length + (LabAut.inputOf tsb).length with hA0
      refine ⟨pn * (A0 + qd), fun n => ?_⟩
      by_cases hn : A0 ≤ n
      · set k := (n - A0) / qd with hk
        refine ⟨LabAut.inputOf (tsa ++ catPow c k ++ tsb), ?_, ?_⟩
        · have hkq : k * qd ≤ n - A0 := Nat.div_mul_le_self _ _
          simp only [LabAut.inputOf_append, List.length_append, inputOf_catPow, hcin]
          omega
        · have hrel : M.rel (LabAut.inputOf (tsa ++ catPow c k ++ tsb))
              (NFAO.outputOf (tsa ++ catPow c k ++ tsb)) :=
            ⟨_, ⟨q₀, h₀, pf, hpf, (hpa.append (path_catPow hcpath k)).append hpb⟩, rfl, rfl⟩
          rw [hM] at hrel
          rw [← hrel]
          have houts : (NFAO.outputOf (tsa ++ catPow c k ++ tsb)).length
              = (NFAO.outputOf tsa).length + k * pn + (NFAO.outputOf tsb).length := by
            simp only [NFAO.outputOf_append, List.length_append, outputOf_catPow, hcout]
          rw [houts]
          have hkq : n - A0 < (k + 1) * qd :=
            (Nat.div_lt_iff_lt_mul hqpos).1 (Nat.lt_succ_self k)
          have h1 : n ≤ k * qd + A0 + qd := by
            have : n - A0 < k * qd + qd := by
              rw [add_mul, one_mul] at hkq; exact hkq
            omega
          calc pn * n ≤ pn * (k * qd + A0 + qd) := Nat.mul_le_mul_left _ h1
            _ = qd * (k * pn) + pn * (A0 + qd) := by ring
            _ ≤ qd * ((NFAO.outputOf tsa).length + k * pn + (NFAO.outputOf tsb).length)
                  + pn * (A0 + qd) := by
                have : k * pn ≤ (NFAO.outputOf tsa).length + k * pn +
                    (NFAO.outputOf tsb).length := by omega
                exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _
      · refine ⟨[], by simp, ?_⟩
        have : pn * n ≤ pn * (A0 + qd) := Nat.mul_le_mul_left _ (by omega)
        omega
  obtain ⟨C₂, hC₂⟩ := hlower
  refine ⟨pn, qd, qd * (Bmax * S.length) + C₂, hqpos, fun n => ⟨?_, ?_⟩⟩
  · intro w hw
    have := hupper w
    have h2 : pn * w.length ≤ pn * n := Nat.mul_le_mul_left _ hw
    omega
  · obtain ⟨w, hw, hle⟩ := hC₂ n
    exact ⟨w, hw, by omega⟩

end CycleMean

end Transducers.Exercises
