/-
The growth of the set of outputs of a rational function, from the loop analysis of
`RequestProject/Exercises/RegularGrowth.lean`.
-/
import RequestProject.Exercises.RegularGrowth
import RequestProject.Exercises.RatInjective

/-!
# The growth of a rational function

The number of outputs of a rational function `f` on the inputs of length at most `n` is compared
here with the number of words of length at most `m` in the *range* of `f`, which is a regular
language (`Transducers.Exercises.rationalRel_range_isRegular`, Exercise
`exer:regular-languages-for-rational-relations`).  The two counting functions are polynomially
equivalent, because

* the output of a rational function is of linearly bounded length
  (`Transducers.Exercises.exists_output_length_bound`, an immediate consequence of the fact that a
  rational function is computed by a bimachine, Theorem `thm:bimachines`), and
* every word of the range has a preimage of linearly bounded length
  (`Transducers.Exercises.exists_short_preimage`), which follows from the previous point applied to
  a rational section of `f`, obtained from the Uniformisation Lemma `lem:uniformisation`.

The growth gap theorem for regular languages
(`Transducers.Exercises.regular_growth_dichotomy`) therefore transfers to rational functions:

* `Transducers.Exercises.rationalFun_growth_dichotomy` — the number of outputs is either
  super-polynomial or `Θ(n^k)` for some `k`;
* `Transducers.Exercises.rationalFun_loop_of_superPoly` — a rational function with
  super-polynomially many outputs has two loops in its range, and hence an injectively encoded copy
  of `{0,1}*` in its range.
-/

namespace Transducers.Exercises

open Transducers

/-! ### Rational functions with a constant prefix and suffix -/

/-- The bimachine computing `w ↦ p ++ φ(w) ++ s`, where `φ` is a homomorphism: the prefix
automaton only remembers whether the gap is the leftmost one, and the suffix automaton remembers
the first letter of the suffix. -/
def constHomBim {A B : Type} (p s : List B) (φ : A → List B) : Bimachine A B Bool (Option A) where
  prefixInit := true
  prefixStep := fun _ _ => false
  suffixInit := none
  suffixStep := fun _ a => some a
  out := fun b t =>
    (if b then p else []) ++ (match t with | none => s | some a => φ a)

lemma constHomBim_evalFrom_false {A B : Type} (p s : List B) (φ : A → List B) (w : List A) :
    (constHomBim p s φ).evalFrom false w = homOf φ w ++ s := by
  induction w with
  | nil =>
      rw [Bimachine.evalFrom_nil]
      simp [constHomBim, homOf]
  | cons a w ih =>
      have h : (constHomBim p s φ).evalFrom false (a :: w)
          = φ a ++ (constHomBim p s φ).evalFrom false w := by
        rw [Bimachine.evalFrom_cons', bmSfx_cons]
        rfl
      rw [h, ih]
      simp [homOf]

lemma constHomBim_eval {A B : Type} (p s : List B) (φ : A → List B) (w : List A) :
    (constHomBim p s φ).eval w = p ++ homOf φ w ++ s := by
  cases w with
  | nil =>
      rw [Bimachine.eval_eq_evalFrom, Bimachine.evalFrom_nil]
      simp [constHomBim, homOf]
  | cons a w =>
      rw [Bimachine.eval_eq_evalFrom, Bimachine.evalFrom_cons', bmSfx_cons,
        show (constHomBim p s φ).prefixStep (constHomBim p s φ).prefixInit a = false from rfl,
        constHomBim_evalFrom_false]
      simp [constHomBim, homOf]

/-- The function `w ↦ p ++ φ(w) ++ s`, for a homomorphism `φ` and constant words `p` and `s`, is
rational. -/
theorem isRationalFun_constHom {A B : Type} [Finite A] [Finite B] (p s : List B)
    (φ : A → List B) : IsRationalFun (fun w : List A => p ++ homOf φ w ++ s) :=
  isRationalFun_of_bimachine (constHomBim p s φ) (fun w => constHomBim_eval p s φ w)

/-- The word obtained by following a sequence of bits along two loops is the image of that
sequence under a homomorphism. -/
lemma cycleWord_eq_homOf {A : Type} (x y : List A) (u : List Bool) :
    cycleWord x y u = homOf (fun b : Bool => if b then x else y) u := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [cycleWord_cons, homOf, ih]

/-! ### The output of a rational function is of linearly bounded length -/

/-- The output of a bimachine is of linearly bounded length: one bounded block per gap. -/
theorem bimachine_output_length_bound {A B P S : Type} [Finite P] [Finite S]
    (M : Bimachine A B P S) :
    ∃ C : ℕ, ∀ w : List A, (M.eval w).length ≤ C * (w.length + 1) := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  haveI : Fintype S := Fintype.ofFinite S
  refine ⟨(Finset.univ : Finset (P × S)).sup (fun ps => (M.out ps.1 ps.2).length), fun w => ?_⟩
  set C := (Finset.univ : Finset (P × S)).sup (fun ps => (M.out ps.1 ps.2).length) with hC
  have hbound : ∀ (p : P) (s : S), (M.out p s).length ≤ C :=
    fun p s => Finset.le_sup (f := fun ps : P × S => (M.out ps.1 ps.2).length)
      (Finset.mem_univ (p, s))
  rw [Bimachine.eval, List.length_flatten, List.map_map]
  calc ((List.range (w.length + 1)).map _).sum
      ≤ ((List.range (w.length + 1)).map (fun _ => C)).sum := by
        refine List.sum_le_sum ?_
        intro i _
        exact hbound _ _
    _ = C * (w.length + 1) := by
        simp [List.sum_replicate, Nat.mul_comm]

/-- **The output of a rational function is of linearly bounded length.**  This is immediate from
Theorem `thm:bimachines`: a rational function is computed by a bimachine, which writes a bounded
block of letters at each of the `|w| + 1` gaps of the input. -/
theorem exists_output_length_bound {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) : ∃ C : ℕ, ∀ w : List A, (f w).length ≤ C * (w.length + 1) := by
  obtain ⟨P, S, _, _, M, hM⟩ := isBimachine_of_rationalFun hf
  obtain ⟨C, hC⟩ := bimachine_output_length_bound M
  exact ⟨C, fun w => by rw [← congrFun hM w]; exact hC w⟩

/-! ### A rational section, and short preimages -/

/-- **A rational section of a rational function.**  Every rational function `f` has a rational
`g` which picks, for a word of the range of `f`, some preimage of it.  This is the Uniformisation
Lemma `lem:uniformisation` applied to the inverse of `f`, made total by sending the words outside
the range — a regular language — to the empty word; it is the argument of
`Transducers.Exercises.exists_rationalFun_inverse_of_injective`, without the injectivity. -/
theorem exists_rationalFun_section {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) :
    ∃ g : List B → List A, IsRationalFun g ∧ ∀ v : List B, (∃ w, v = f w) → f (g v) = v := by
  set L : Language B := {v | ∃ w, v = f w} with hL
  have hLreg : L.IsRegular := rationalRel_range_isRegular hf
  have hrat : IsRationalRel (fun (v : List B) (u : List A) => v = f u ∨ (v ∈ Lᶜ ∧ u = [])) :=
    isRationalRel_union (isRationalRel_inv hf) (isRationalRel_regular_to_nil hLreg.compl)
  have htot : ∀ v : List B, ∃ u : List A, v = f u ∨ (v ∈ Lᶜ ∧ u = []) := by
    intro v
    by_cases hv : v ∈ L
    · obtain ⟨w, hw⟩ := hv
      exact ⟨w, Or.inl hw⟩
    · exact ⟨[], Or.inr ⟨hv, rfl⟩⟩
  obtain ⟨g, hg, hgspec⟩ := exists_rationalFun_of_total_rel hrat htot
  refine ⟨g, hg, fun v hv => ?_⟩
  rcases hgspec v with h | ⟨hmem, -⟩
  · exact h.symm
  · exact absurd hv hmem

/-- **Short preimages.**  Every word of the range of a rational function has a preimage of
linearly bounded length: apply the length bound to a rational section. -/
theorem exists_short_preimage {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) :
    ∃ D : ℕ, ∀ v : List B, (∃ w, v = f w) →
      ∃ w : List A, f w = v ∧ w.length ≤ D * (v.length + 1) := by
  obtain ⟨g, hg, hgspec⟩ := exists_rationalFun_section hf
  obtain ⟨D, hD⟩ := exists_output_length_bound hg
  exact ⟨D, fun v hv => ⟨g v, hgspec v hv, hD v⟩⟩

/-! ### Comparing the two counting functions -/

/-- The set of outputs of `f` on the inputs of length at most `n` is finite. -/
lemma finite_outSet {A B : Type} [Finite A] {f : List A → List B} (n : ℕ) :
    (f '' {w : List A | w.length ≤ n}).Finite :=
  (finite_lists_length_le n).image _

lemma outSet_ncard_le_langCount {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    {C : ℕ} (hC : ∀ w : List A, (f w).length ≤ C * (w.length + 1)) (n : ℕ) :
    (f '' {w : List A | w.length ≤ n}).ncard ≤ langCount ({v | ∃ w, v = f w} : Language B)
      (C * (n + 1)) := by
  refine Set.ncard_le_ncard ?_ ?_
  · rintro v ⟨w, hw, rfl⟩
    exact ⟨⟨w, rfl⟩, le_trans (hC w) (Nat.mul_le_mul_left C (by simpa using hw))⟩
  · exact (finite_lists_length_le (C * (n + 1))).subset (fun v hv => hv.2)

lemma langCount_le_outSet_ncard {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    {D : ℕ} (hD : ∀ v : List B, (∃ w, v = f w) →
      ∃ w : List A, f w = v ∧ w.length ≤ D * (v.length + 1)) (m : ℕ) :
    langCount ({v | ∃ w, v = f w} : Language B) m
      ≤ (f '' {w : List A | w.length ≤ D * (m + 1)}).ncard := by
  refine Set.ncard_le_ncard ?_ (finite_outSet _)
  rintro v ⟨hv, hlen⟩
  obtain ⟨w, hw, hwlen⟩ := hD v hv
  exact ⟨w, le_trans hwlen (Nat.mul_le_mul_left D (by omega)), hw⟩

/-- The number of outputs on the inputs of length at most `n` grows with `n`. -/
lemma outSet_ncard_mono {A B : Type} [Finite A] {f : List A → List B} {m n : ℕ} (h : m ≤ n) :
    (f '' {w : List A | w.length ≤ m}).ncard ≤ (f '' {w : List A | w.length ≤ n}).ncard :=
  Set.ncard_le_ncard (Set.image_mono (fun _ hw => le_trans hw h)) (finite_outSet n)

/-- A polynomial bound on the number of words of the range gives a polynomial bound on the
number of outputs. -/
lemma outSet_ncard_le_of_langCount_le {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    {C0 K k : ℕ} (hC0 : ∀ w : List A, (f w).length ≤ C0 * (w.length + 1))
    (hK : ∀ m, langCount ({v | ∃ w, v = f w} : Language B) m ≤ K * (m + 1) ^ k) (n : ℕ) :
    (f '' {w : List A | w.length ≤ n}).ncard ≤ K * (C0 + 1) ^ k * (n + 1) ^ k := by
  have hstep : C0 * (n + 1) + 1 ≤ (C0 + 1) * (n + 1) := by
    have h : (C0 + 1) * (n + 1) = C0 * (n + 1) + (n + 1) := by ring
    rw [h]
    exact Nat.add_le_add_left (by omega) _
  calc (f '' {w : List A | w.length ≤ n}).ncard
      ≤ langCount ({v | ∃ w, v = f w} : Language B) (C0 * (n + 1)) :=
        outSet_ncard_le_langCount hC0 n
    _ ≤ K * (C0 * (n + 1) + 1) ^ k := hK _
    _ ≤ K * ((C0 + 1) * (n + 1)) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hstep k)
    _ = K * (C0 + 1) ^ k * (n + 1) ^ k := by rw [mul_pow, mul_assoc]

/-- **Two loops in the range give super-polynomially many outputs.**  Following a sequence of `j`
bits along the two loops produces `2 ^ j` words of the range, of length linear in `j`, and each of
them has a preimage of length linear in `j`. -/
lemma outSet_superPoly_of_range_loops {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    {D : ℕ} (hD : ∀ v : List B, (∃ w, v = f w) →
      ∃ w : List A, f w = v ∧ w.length ≤ D * (v.length + 1))
    {p x y s : List B} (hxpos : 0 < x.length) (hlen : x.length = y.length) (hxy : x ≠ y)
    (hmem : ∀ u : List Bool, ∃ w : List A, p ++ cycleWord x y u ++ s = f w) :
    ∀ k C : ℕ, ∃ n, C * (n + 1) ^ k < (f '' {w : List A | w.length ≤ n}).ncard := by
  classical
  -- the bound on the length of a preimage of the word encoding `j` bits
  have hlb : ∀ j : ℕ, 2 ^ j ≤
      (f '' {w : List A | w.length ≤ D * (p.length + j * x.length + s.length + 1)}).ncard := by
    intro j
    set n := D * (p.length + j * x.length + s.length + 1) with hn
    set T : Set (List B) := f '' {w : List A | w.length ≤ n} with hT
    have hTfin : T.Finite := finite_outSet n
    haveI : Finite T := hTfin.to_subtype
    have hmemT : ∀ t : Fin j → Bool,
        p ++ cycleWord x y (List.ofFn t) ++ s ∈ T := by
      intro t
      obtain ⟨w0, hw0⟩ := hmem (List.ofFn t)
      obtain ⟨w, hw, hwlen⟩ := hD _ ⟨w0, hw0⟩
      refine ⟨w, ?_, hw⟩
      refine le_trans hwlen (Nat.mul_le_mul_left D ?_)
      simp only [List.length_append, cycleWord_length hlen, List.length_ofFn]
      omega
    have hinj : Function.Injective
        (fun t : Fin j → Bool => (⟨p ++ cycleWord x y (List.ofFn t) ++ s, hmemT t⟩ : T)) := by
      intro t t' htt
      have h1 : p ++ cycleWord x y (List.ofFn t) ++ s
          = p ++ cycleWord x y (List.ofFn t') ++ s := congrArg Subtype.val htt
      have h2 := List.append_cancel_left (List.append_cancel_right h1)
      exact List.ofFn_injective (cycleWord_injective hlen hxpos hxy h2)
    have hcard : Nat.card (Fin j → Bool) = 2 ^ j := by simp [Nat.card_eq_fintype_card]
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcard] at hle
    calc 2 ^ j ≤ Nat.card T := hle
      _ = T.ncard := rfl
  intro k C
  obtain ⟨E, hE⟩ : ∃ E, E = D * (p.length + x.length + s.length + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨m, hm1, hm⟩ := exists_poly_lt_two_pow (C * E ^ k) k
  refine ⟨D * (p.length + m * x.length + s.length + 1), ?_⟩
  have hin : p.length + m * x.length + s.length + 1
      ≤ m * (p.length + x.length + s.length + 1) := by nlinarith
  have hstep : D * (p.length + m * x.length + s.length + 1) + 1 ≤ E * m := by
    have h1 : D * (p.length + m * x.length + s.length + 1)
        ≤ D * (m * (p.length + x.length + s.length + 1)) := Nat.mul_le_mul_left _ hin
    have h2 : E * m = D * (m * (p.length + x.length + s.length + 1)) + m := by rw [hE]; ring
    omega
  calc C * (D * (p.length + m * x.length + s.length + 1) + 1) ^ k ≤ C * (E * m) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hstep k)
    _ = C * E ^ k * m ^ k := by rw [mul_pow, mul_assoc]
    _ < 2 ^ m := hm
    _ ≤ (f '' {w : List A |
            w.length ≤ D * (p.length + m * x.length + s.length + 1)}).ncard := hlb m

/-! ### The dichotomy -/

/-- **The growth of a rational function has no gaps.**  The number of outputs of a rational
function on the inputs of length at most `n` is either super-polynomial, or `Θ(n^k)` for some
`k`.  This is the growth gap theorem for regular languages
(`Transducers.Exercises.regular_growth_dichotomy`), transported along the polynomial equivalence
between the number of outputs and the number of words of the range. -/
theorem rationalFun_growth_dichotomy {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) :
    (∀ k C : ℕ, ∃ n, C * (n + 1) ^ k < (f '' {w : List A | w.length ≤ n}).ncard) ∨
      ∃ k : ℕ, (∃ C : ℕ, ∀ n, (f '' {w : List A | w.length ≤ n}).ncard ≤ C * (n + 1) ^ k) ∧
        ∃ c : ℕ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n →
          (n + 1) ^ k ≤ c * (f '' {w : List A | w.length ≤ n}).ncard := by
  classical
  have hLreg : Language.IsRegular ({v | ∃ w, v = f w} : Language B) :=
    rationalRel_range_isRegular hf
  have hnel : ∃ v, v ∈ ({v | ∃ w, v = f w} : Language B) := ⟨f [], [], rfl⟩
  obtain ⟨C0, hC0⟩ := exists_output_length_bound hf
  obtain ⟨D, hD⟩ := exists_short_preimage hf
  rcases regular_growth_dichotomy hLreg hnel with
    ⟨p, x, y, s, hxpos, hlen, hxy, hmem⟩ | ⟨k, ⟨K, hK⟩, c, hcpos, N, hN⟩
  · exact Or.inl (outSet_superPoly_of_range_loops hD hxpos hlen hxy hmem)
  · refine Or.inr ⟨k, ⟨K * (C0 + 1) ^ k, outSet_ncard_le_of_langCount_le hC0 hK⟩,
      c * (2 * (D + 1)) ^ k, ?_, (D + 1) * (N + 1), fun n hn => ?_⟩
    · exact Nat.mul_pos hcpos (Nat.pow_pos (by omega))
    · have hd0 : 0 < D + 1 := Nat.succ_pos D
      obtain ⟨q, hqdef⟩ : ∃ q, q = n / (D + 1) := ⟨_, rfl⟩
      have hdm : (D + 1) * q + n % (D + 1) = n := by rw [hqdef]; exact Nat.div_add_mod n (D + 1)
      have hmod : n % (D + 1) < D + 1 := Nat.mod_lt _ hd0
      have hqN : N + 1 ≤ q := by
        rw [hqdef]
        refine (Nat.le_div_iff_mul_le hd0).mpr ?_
        calc (N + 1) * (D + 1) = (D + 1) * (N + 1) := by ring
          _ ≤ n := hn
      obtain ⟨m, hmdef⟩ : ∃ m, m + 1 = q := ⟨q - 1, by omega⟩
      have hmN : N ≤ m := by omega
      have hPle : D + 1 ≤ (D + 1) * (m + 1) := by
        rw [hmdef]
        exact Nat.le_mul_of_pos_right _ (by omega)
      have hPn : (D + 1) * (m + 1) ≤ n := by rw [hmdef]; omega
      have hPn2 : n < (D + 1) * (m + 1) + (D + 1) := by rw [hmdef]; omega
      have hn1 : n + 1 ≤ 2 * ((D + 1) * (m + 1)) := by omega
      have hDn : D * (m + 1) ≤ n :=
        le_trans (Nat.mul_le_mul_right _ (by omega)) hPn
      have hstep1 : langCount ({v | ∃ w, v = f w} : Language B) m
          ≤ (f '' {w : List A | w.length ≤ n}).ncard :=
        le_trans (langCount_le_outSet_ncard hD m) (outSet_ncard_mono hDn)
      have hstep2 : (m + 1) ^ k ≤ c * (f '' {w : List A | w.length ≤ n}).ncard :=
        le_trans (hN m hmN) (Nat.mul_le_mul_left c hstep1)
      calc (n + 1) ^ k ≤ (2 * ((D + 1) * (m + 1))) ^ k := Nat.pow_le_pow_left hn1 k
        _ = (2 * (D + 1)) ^ k * (m + 1) ^ k := by rw [← mul_assoc, mul_pow]
        _ ≤ (2 * (D + 1)) ^ k * (c * (f '' {w : List A | w.length ≤ n}).ncard) :=
            Nat.mul_le_mul_left _ hstep2
        _ = c * (2 * (D + 1)) ^ k * (f '' {w : List A | w.length ≤ n}).ncard := by ring

/-- **A rational function with super-polynomially many outputs has two loops in its range.**
The range is a regular language of super-polynomial growth, so an automaton for it has two loops
of the same length with different labels on a state that is both reachable and co-reachable; the
words obtained by following a sequence of bits along those two loops are all in the range. -/
theorem rationalFun_loop_of_superPoly {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f)
    (hs : ∀ k C : ℕ, ∃ n, C * (n + 1) ^ k < (f '' {w : List A | w.length ≤ n}).ncard) :
    ∃ p x y s : List B, 0 < x.length ∧ x.length = y.length ∧ x ≠ y ∧
      ∀ u : List Bool, ∃ w : List A, f w = p ++ cycleWord x y u ++ s := by
  classical
  have hLreg : Language.IsRegular ({v | ∃ w, v = f w} : Language B) :=
    rationalRel_range_isRegular hf
  have hnel : ∃ v, v ∈ ({v | ∃ w, v = f w} : Language B) := ⟨f [], [], rfl⟩
  rcases regular_growth_dichotomy hLreg hnel with
    ⟨p, x, y, s, hxpos, hlen, hxy, hmem⟩ | ⟨k, ⟨K, hK⟩, -⟩
  · exact ⟨p, x, y, s, hxpos, hlen, hxy, fun u => (hmem u).imp fun _ h => h.symm⟩
  · exfalso
    obtain ⟨C0, hC0⟩ := exists_output_length_bound hf
    obtain ⟨n, hn⟩ := hs k (K * (C0 + 1) ^ k)
    exact absurd (outSet_ncard_le_of_langCount_le hC0 hK n) (by omega)

/-- **The identity of `{0,1}*` from two loops in the range.**  Two loops of the same length with
different labels in the range of `f` give an injective rational encoding `enc` of `{0,1}*` inside
that range; a rational section of `f` (the Uniformisation Lemma) turns a bit string into an input
of `f` mapped to its encoding, and the rational left inverse of `enc` (Exercise
`exer:rational-injectivity-decidable`) reads the bits back. -/
theorem exists_rational_bool_identity_of_range_loops {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) {p x y s : List B}
    (hxpos : 0 < x.length) (hlen : x.length = y.length) (hxy : x ≠ y)
    (hmem : ∀ u : List Bool, ∃ w : List A, f w = p ++ cycleWord x y u ++ s) :
    ∃ (g : List Bool → List A) (h : List B → List Bool),
      IsRationalFun g ∧ IsRationalFun h ∧ ∀ u : List Bool, h (f (g u)) = u := by
  classical
  have hencrat : IsRationalFun
      (fun u : List Bool => p ++ homOf (fun b : Bool => if b then x else y) u ++ s) :=
    isRationalFun_constHom p s _
  have hencval : ∀ u : List Bool,
      p ++ homOf (fun b : Bool => if b then x else y) u ++ s = p ++ cycleWord x y u ++ s := by
    intro u
    rw [cycleWord_eq_homOf]
  have hencinj : Function.Injective
      (fun u : List Bool => p ++ homOf (fun b : Bool => if b then x else y) u ++ s) := by
    intro u u' hu
    simp only [hencval] at hu
    exact cycleWord_injective hlen hxpos hxy
      (List.append_cancel_left (List.append_cancel_right hu))
  obtain ⟨h, hhrat, hh⟩ := exists_rationalFun_inverse_of_injective hencrat hencinj
  obtain ⟨g0, hg0rat, hg0⟩ := exists_rationalFun_section hf
  refine ⟨fun u => g0 (p ++ homOf (fun b : Bool => if b then x else y) u ++ s), h,
    isRationalFun_comp hencrat hg0rat, hhrat, fun u => ?_⟩
  have hin : ∃ w, p ++ homOf (fun b : Bool => if b then x else y) u ++ s = f w := by
    obtain ⟨w, hw⟩ := hmem u
    exact ⟨w, by rw [hencval]; exact hw.symm⟩
  rw [hg0 _ hin]
  exact hh u

/-- **The identity of `{0,1}*` inside a rational function with super-polynomially many outputs.**
The range of such a function has two loops
(`Transducers.Exercises.rationalFun_loop_of_superPoly`), and two loops give the identity
(`Transducers.Exercises.exists_rational_bool_identity_of_range_loops`). -/
theorem exists_rational_bool_identity_of_superPoly {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f)
    (hs : ∀ k C : ℕ, ∃ n, C * (n + 1) ^ k < (f '' {w : List A | w.length ≤ n}).ncard) :
    ∃ (g : List Bool → List A) (h : List B → List Bool),
      IsRationalFun g ∧ IsRationalFun h ∧ ∀ u : List Bool, h (f (g u)) = u := by
  obtain ⟨p, x, y, s, hxpos, hlen, hxy, hmem⟩ := rationalFun_loop_of_superPoly hf hs
  exact exists_rational_bool_identity_of_range_loops hf hxpos hlen hxy hmem

end Transducers.Exercises
