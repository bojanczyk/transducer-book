/-
Exercise `exer:regular-compression` of the chapter *Regular functions, introduction*
(`regular-intro.tex`) of *Transducers* (M. Bojańczyk): regular functions are compatible with
compression.

Exercise `exer:rational-compression` calls a function *compatible with compression* when there is a
polynomial time algorithm which inputs a grammar compression of a string and outputs a grammar
compression of its image.  Polynomial time is not modelled in this project, so what is proved here
is the size half of that statement, exactly as in
`RequestProject/Exercises/Compression.lean` for Exercise
`exer:polyregular-marked-squaring-compression`: for a regular `f` there are `C` and `k` such that
every string with a compression of `n` rules has an image with a compression of at most `C * n ^ k`
rules (`Transducers.Exercises.CompatCompression`).  The two exercises are then about the same
quantity: the marked square of `aᴺ` has *no* small compression, whereas the image of every regular
function does.  The divergence is recorded in `EXERCISES.md`.

The proof is the one of the book.  Compatibility is closed under composition, so it is enough to
treat the three prime regular functions of Definition `def:regular-functions`: the rational
functions, map reverse and map duplicate.  For a rational function the compression is built from a
bimachine (Theorem `thm:bimachines`), one nonterminal per rule and pair of states; for the two
others one uses Claim `claim:map-compression` of the solution -- compatibility is preserved by map
lifting -- together with the fact that reversing and duplicating a compression is immediate.
-/
import RequestProject.Exercises.CompressionRat
import RequestProject.Exercises.CompressionMapLift
import RequestProject.PartC.RegularDef

namespace Transducers
namespace Exercises

variable {A B C : Type}

/-! ## Compatibility with compression -/

/-- A function is *compatible with compression* (in the size sense: see the header of this file)
when the image of a string with a compression of `n` rules has a compression with at most
`C * n ^ k` rules, for constants `C` and `k` depending only on the function. -/
def CompatCompression (f : List A → List B) : Prop :=
  ∃ C k : ℕ, ∀ (rs : List (Rule A)) (w : List A), Generates rs w →
    ∃ rs' : List (Rule B), Generates rs' (f w) ∧ rs'.length ≤ C * rs.length ^ k

lemma CompatCompression.congr {f g : List A → List B} (hf : CompatCompression f)
    (h : ∀ w, f w = g w) : CompatCompression g := by
  obtain ⟨C, k, hC⟩ := hf
  exact ⟨C, k, fun rs w hw => by
    obtain ⟨rs', h1, h2⟩ := hC rs w hw
    exact ⟨rs', (h w) ▸ h1, h2⟩⟩

lemma compatCompression_id : CompatCompression (id : List A → List A) :=
  ⟨1, 1, fun rs w hw => ⟨rs, hw, by simp⟩⟩

/-- Compatibility with compression is closed under composition. -/
lemma CompatCompression.comp {f : List A → List B} {g : List B → List C}
    (hf : CompatCompression f) (hg : CompatCompression g) : CompatCompression (g ∘ f) := by
  obtain ⟨C₁, k₁, h₁⟩ := hf
  obtain ⟨C₂, k₂, h₂⟩ := hg
  refine ⟨C₂ * C₁ ^ k₂, k₁ * k₂, fun rs w hw => ?_⟩
  obtain ⟨ss, hss, hlen⟩ := h₁ rs w hw
  obtain ⟨ts, hts, hlen'⟩ := h₂ ss (f w) hss
  refine ⟨ts, hts, hlen'.trans ?_⟩
  calc C₂ * ss.length ^ k₂ ≤ C₂ * (C₁ * rs.length ^ k₁) ^ k₂ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _)
    _ = C₂ * C₁ ^ k₂ * rs.length ^ (k₁ * k₂) := by
        rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.mul_assoc]

/-! ## The easy operations on compressions -/

/-- A letter-to-letter map is compatible with compression. -/
lemma compatCompression_map (h : A → B) :
    CompatCompression (fun w : List A => w.map h) :=
  ⟨1, 1, fun rs w hw => ⟨rs.map (mapRule h), generates_map hw, by simp⟩⟩

/-- Reversing a compression. -/
def revRule : Rule A → Rule A
  | Rule.letter a => Rule.letter a
  | Rule.cat j k => Rule.cat k j

lemma slpVal_rev (rs : List (Rule A)) :
    ∀ i, slpVal (rs.map revRule) i = (slpVal rs i).reverse := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hget : (rs.map revRule)[i]? = (rs[i]?).map revRule := List.getElem?_map ..
    rcases hr : rs[i]? with _ | r
    · rw [hr] at hget
      rw [slpVal_of_getElem?_none (by simpa using hget), slpVal_of_getElem?_none hr]
      rfl
    · rw [hr] at hget
      cases r with
      | letter a =>
          rw [slpVal_letter (by simpa [revRule] using hget), slpVal_letter hr]
          rfl
      | cat j k =>
          have hget' : (rs.map revRule)[i]? = some (Rule.cat k j) := by
            simpa [revRule] using hget
          by_cases hjk : j < i ∧ k < i
          · rw [slpVal_cat hget' hjk.2 hjk.1, slpVal_cat hr hjk.1 hjk.2, ih j hjk.1, ih k hjk.2,
              List.reverse_append]
          · rw [slpVal_cat_bad hget' (by tauto), slpVal_cat_bad hr hjk]
            rfl

/-- Reversal is compatible with compression. -/
lemma compatCompression_reverse : CompatCompression (List.reverse : List A → List A) := by
  refine ⟨1, 1, fun rs w hw => ⟨rs.map revRule, ⟨by simpa using hw.1, ?_⟩, by simp⟩⟩
  rw [List.length_map, slpVal_rev, hw.2]

/-- Duplication is compatible with compression. -/
lemma compatCompression_dup : CompatCompression (fun w : List A => w ++ w) := by
  refine ⟨3, 1, fun rs w hw => ⟨catSLP rs rs, generates_catSLP hw hw, ?_⟩⟩
  rw [length_catSLP, pow_one]
  have : 1 ≤ rs.length := List.length_pos_iff.2 hw.1
  omega

/-! ## The two substantial steps -/

/-- **Exercise `exer:rational-compression`, size half.**  A rational function is compatible with
compression: the compression of the image is built from a bimachine for the function, with one
nonterminal for every rule of the given compression and every pair of a state of the prefix
automaton and a state of the suffix automaton. -/
theorem compatCompression_of_isRationalFun [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) : CompatCompression f := by
  obtain ⟨P, S, hP, hS, M, hM⟩ := ((rational_iff_unambiguous_iff_bimachine f).out 0 2).1 hf
  haveI := hP
  haveI := hS
  obtain ⟨C, hC⟩ := exists_slp_of_bimachine M
  refine ⟨C, 1, fun rs w hw => ?_⟩
  obtain ⟨rs', h1, h2⟩ := hC rs w hw
  exact ⟨rs', by rwa [← hM], by simpa using h2⟩

/-- **Claim `claim:map-compression`.**  Compatibility with compression is preserved by map
lifting. -/
theorem CompatCompression.mapLift {f : List A → List B} (hf : CompatCompression f) :
    CompatCompression (Transducers.mapLift f) := by
  obtain ⟨C, k, hC⟩ := hf
  exact ⟨3 * C * 23 ^ k + 20, k + 1, exists_slp_of_mapLift hC⟩

/-! ## The exercise -/

/-- **Exercise `exer:regular-compression`**, auxiliary form: the finiteness of the two alphabets is
carried as an explicit hypothesis, so that the induction on the composition tree has access to the
finiteness of the intermediate alphabets. -/
theorem compatCompression_of_isRegularFun_aux {A B : Type} {f : List A → List B}
    (hf : IsRegularFun f) : Finite A → Finite B → CompatCompression f := by
  induction hf with
  | @base A B f h =>
      intro hA hB
      haveI := hA; haveI := hB
      rcases h with hrat | ⟨A₀, e, e', hfe⟩ | ⟨A₀, e, e', hfe⟩
      · exact compatCompression_of_isRationalFun hrat
      · exact ((((compatCompression_map (e : A → Option A₀)).comp
            (CompatCompression.mapLift (compatCompression_reverse (A := A₀)))).comp
            (compatCompression_map (e'.symm : Option A₀ → B)))).congr (fun w => (hfe w).symm)
      · exact ((((compatCompression_map (e : A → Option A₀)).comp
            (CompatCompression.mapLift (compatCompression_dup (A := A₀)))).comp
            (compatCompression_map (e'.symm : Option A₀ → B)))).congr (fun w => (hfe w).symm)
  | id A => intro _ _; exact compatCompression_id
  | @comp A B C hB f g _ _ ihf ihg =>
      intro hA hC
      haveI := hA; haveI := hB; haveI := hC
      exact (ihf hA hB).comp (ihg hB hC)

/-- **Exercise `exer:regular-compression`.**  Every regular function is compatible with
compression, in the size sense of `CompatCompression`. -/
theorem compatCompression_of_isRegularFun {f : List A → List B} [Finite A] [Finite B]
    (hf : IsRegularFun f) : CompatCompression f :=
  compatCompression_of_isRegularFun_aux hf ‹_› ‹_›

end Exercises
end Transducers
