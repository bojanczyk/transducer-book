/-
The rational case of Exercise `exer:regular-compression` of the chapter *Regular functions,
introduction* (`regular-intro.tex`) of *Transducers* (M. Bojańczyk), which is also the size half of
Exercise `exer:rational-compression`: the image of a compressed string under a rational function has
a compression of linear size.

The construction is the one of the book.  A rational function is computed by a bimachine (Theorem
`thm:bimachines`), which produces, for every gap of the input string, an output block determined by
the state of the prefix automaton on the prefix and the state of the suffix automaton on the
suffix.  For a factor `u` of the input write `bimGaps M u p s` for the concatenation of the blocks
produced at the gaps of `u` other than its right end, when the prefix automaton enters `u` in the
state `p` and the suffix automaton enters `u` from the right in the state `s`.  This quantity is
compositional,

  `bimGaps M (u ++ v) p s = bimGaps M u p (δ_S(v) s) ++ bimGaps M v (δ_P(u) p) s`,

so the compression of the image has one nonterminal for every rule of the given compression and
every pair of a state of the prefix automaton and a state of the suffix automaton; the block at the
right end of the whole string is appended at the top level.  The block construction
`Transducers.Exercises.exists_blockSLP` performs the bookkeeping.
-/
import RequestProject.Exercises.CompressionSLP
import RequestProject.PartB.RationalStatements

namespace Transducers
namespace Exercises

variable {A B P S : Type}

/-! ## The output of a bimachine at the gaps of a factor -/

/-- The part of the output of the bimachine `M` that is produced at the gaps of `u` other than the
gap at its right end, when the prefix automaton enters `u` in the state `p` and the suffix
automaton -- which reads the input from the right -- enters `u` in the state `s`. -/
def bimGaps (M : Bimachine A B P S) (u : List A) (p : P) (s : S) : List B :=
  ((List.range u.length).map (fun i =>
    M.out (strTrans M.prefixStep (u.take i) p)
          (strTrans M.suffixStep (u.drop i).reverse s))).flatten

@[simp] lemma bimGaps_nil (M : Bimachine A B P S) (p : P) (s : S) : bimGaps M [] p s = [] := by
  simp [bimGaps]

private lemma strTransApp {Q : Type} (δ : Q → A → Q) (u v : List A) (q : Q) :
    strTrans δ (u ++ v) q = strTrans δ v (strTrans δ u q) := by
  simp [strTrans]

lemma bimGaps_singleton (M : Bimachine A B P S) (a : A) (p : P) (s : S) :
    bimGaps M [a] p s = M.out p (strTrans M.suffixStep [a] s) := by
  simp [bimGaps, strTrans]

/-- The gap output of a concatenation: the gaps of the left factor are read with the state that the
suffix automaton has at the middle gap, those of the right factor with the state that the prefix
automaton has there. -/
lemma bimGaps_append (M : Bimachine A B P S) (u v : List A) (p : P) (s : S) :
    bimGaps M (u ++ v) p s =
      bimGaps M u p (strTrans M.suffixStep v.reverse s) ++
        bimGaps M v (strTrans M.prefixStep u p) s := by
  rw [bimGaps, List.length_append, List.range_add, List.map_append, List.flatten_append]
  congr 1
  · rw [bimGaps]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    have hi' : i < u.length := List.mem_range.1 hi
    rw [List.take_append_of_le_length (le_of_lt hi'),
      List.drop_append_of_le_length (le_of_lt hi'), List.reverse_append, strTransApp]
  · rw [bimGaps, List.map_map]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [List.take_length_add_append, List.drop_length_add_append, strTransApp]

/-- The output of a bimachine is the gap output of the whole input, followed by the block produced
at the right end. -/
lemma eval_eq_bimGaps (M : Bimachine A B P S) (w : List A) :
    M.eval w = bimGaps M w M.prefixInit M.suffixInit ++
      M.out (strTrans M.prefixStep w M.prefixInit) M.suffixInit := by
  rw [Bimachine.eval, List.range_succ, List.map_append, List.flatten_append, bimGaps]
  simp [strTrans]

/-! ## The compression of the image -/

/-- The image of a compressed string under a bimachine has a compression of linear size. -/
theorem exists_slp_of_bimachine [Finite P] [Finite S] (M : Bimachine A B P S) :
    ∃ C : ℕ, ∀ (rs : List (Rule A)) (w : List A), Generates rs w →
      ∃ rs' : List (Rule B), Generates rs' (M.eval w) ∧ rs'.length ≤ C * rs.length := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  haveI : Fintype S := Fintype.ofFinite S
  -- the longest output block of the bimachine
  set L : ℕ := (Finset.univ : Finset (P × S)).sup (fun x => (M.out x.1 x.2).length) with hL
  have hout : ∀ (p : P) (s : S), (M.out p s).length ≤ L := by
    intro p s
    exact Finset.le_sup (f := fun x : P × S => (M.out x.1 x.2).length) (Finset.mem_univ (p, s))
  set K : ℕ := 2 * L + 3 with hK
  refine ⟨1 + Fintype.card (P × S) * (K + 5) + 2 * L + 3, ?_⟩
  intro rs w hw
  have hrsl : 0 < rs.length := List.length_pos_iff.2 hw.1
  -- the strings to be computed: one for every rule and every pair of states
  set T : ℕ → P × S → List B := fun i c => bimGaps M (slpVal rs i) c.1 c.2 with hT
  have heps : Generates (epsSLP : List (Rule B)) [] := generates_epsSLP
  have hrec : ∀ i < rs.length, ∀ c : P × S, ∃ (p₁ p₂ : Option (ℕ × (P × S)))
      (s₀ s₁ s₂ : List (Rule B)) (t₀ t₁ t₂ : List B),
      (∀ x ∈ p₁, x.1 < i) ∧ (∀ x ∈ p₂, x.1 < i) ∧
      Generates s₀ t₀ ∧ Generates s₁ t₁ ∧ Generates s₂ t₂ ∧
      s₀.length + s₁.length + s₂.length ≤ K ∧
      T i c = t₀ ++ (p₁.elim [] fun x => T x.1 x.2) ++ t₁ ++
        (p₂.elim [] fun x => T x.1 x.2) ++ t₂ := by
    intro i _ c
    have empty : slpVal rs i = [] → ∃ (p₁ p₂ : Option (ℕ × (P × S)))
        (s₀ s₁ s₂ : List (Rule B)) (t₀ t₁ t₂ : List B),
        (∀ x ∈ p₁, x.1 < i) ∧ (∀ x ∈ p₂, x.1 < i) ∧
        Generates s₀ t₀ ∧ Generates s₁ t₁ ∧ Generates s₂ t₂ ∧
        s₀.length + s₁.length + s₂.length ≤ K ∧
        T i c = t₀ ++ (p₁.elim [] fun x => T x.1 x.2) ++ t₁ ++
          (p₂.elim [] fun x => T x.1 x.2) ++ t₂ := by
      intro h
      refine ⟨none, none, epsSLP, epsSLP, epsSLP, [], [], [], by simp, by simp, heps, heps, heps,
        by simp [hK], ?_⟩
      simp [hT, h]
    rcases hr : rs[i]? with _ | r
    · exact empty (slpVal_of_getElem?_none hr)
    · cases r with
      | letter a =>
          refine ⟨none, none, strSLP (M.out c.1 (strTrans M.suffixStep [a] c.2)), epsSLP, epsSLP,
            M.out c.1 (strTrans M.suffixStep [a] c.2), [], [], by simp, by simp,
            generates_strSLP _, heps, heps, ?_, ?_⟩
          · have := length_strSLP (M.out c.1 (strTrans M.suffixStep [a] c.2))
            have h2 := hout c.1 (strTrans M.suffixStep [a] c.2)
            simp only [length_epsSLP, hK]
            omega
          · simp only [hT, slpVal_letter hr, bimGaps_singleton]
            simp
      | cat j k =>
          by_cases hjk : j < i ∧ k < i
          · refine ⟨some (j, (c.1, strTrans M.suffixStep (slpVal rs k).reverse c.2)),
              some (k, (strTrans M.prefixStep (slpVal rs j) c.1, c.2)),
              epsSLP, epsSLP, epsSLP, [], [], [], ?_, ?_, heps, heps, heps, by simp [hK], ?_⟩
            · intro x hx
              rw [Option.mem_def, Option.some_inj] at hx
              subst hx
              exact hjk.1
            · intro x hx
              rw [Option.mem_def, Option.some_inj] at hx
              subst hx
              exact hjk.2
            · simp only [hT, slpVal_cat hr hjk.1 hjk.2, bimGaps_append, Option.elim]
              simp
          · exact empty (slpVal_cat_bad hr hjk)
  obtain ⟨b, idx, hpos, hbeps, hblen, hidx⟩ := exists_blockSLP T rs.length K hrec
  obtain ⟨hlt, hval⟩ := hidx (rs.length - 1) (by omega) (M.prefixInit, M.suffixInit)
  have hbuild : BuildSt b (idx (rs.length - 1) (M.prefixInit, M.suffixInit))
      (bimGaps M w M.prefixInit M.suffixInit) := by
    refine ⟨hpos, hbeps, hlt, ?_⟩
    rw [hval]
    simp only [hT, hw.2]
  obtain ⟨ss, hss, hsslen⟩ := generates_of_buildSt hbuild
  refine ⟨catSLP ss (strSLP (M.out (strTrans M.prefixStep w M.prefixInit) M.suffixInit)), ?_, ?_⟩
  · rw [eval_eq_bimGaps]
    exact generates_catSLP hss (generates_strSLP _)
  · rw [length_catSLP]
    have h1 := length_strSLP (M.out (strTrans M.prefixStep w M.prefixInit) M.suffixInit)
    have h2 := hout (strTrans M.prefixStep w M.prefixInit) M.suffixInit
    have h3 : ss.length ≤ 1 + rs.length * (Fintype.card (P × S) * (K + 5)) + 1 := by omega
    have h4 : (1 + Fintype.card (P × S) * (K + 5) + 2 * L + 3) * rs.length
        = rs.length + rs.length * (Fintype.card (P × S) * (K + 5)) + (2 * L + 3) * rs.length := by
      ring
    have h5 : 2 * L + 3 ≤ (2 * L + 3) * rs.length := Nat.le_mul_of_pos_right _ hrsl
    omega

end Exercises
end Transducers
