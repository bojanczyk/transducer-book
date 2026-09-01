/-
Exercise `exer:polyregular-unmarked-squaring` of the chapter on polyregular
functions (`polyregular-intro.tex`) of *Transducers* (M. Bojańczyk).
-/
import RequestProject.Exercises.CompressionReg
import RequestProject.PartD.PolyDef

/-!
# Unmarked squaring gives a strictly smaller class than marked squaring

Exercise `exer:polyregular-unmarked-squaring` asks what happens if, in the definition
`def:polyregular-functions` of the polyregular functions, marked squaring is replaced by the
unmarked squaring `w ↦ w^|w|` of `exer:squaring-continuous`: the resulting class is a strict
subset of the polyregular functions.

The solution is the one of the book.  Unmarked squaring is compatible with compression, in the
size sense `Transducers.Exercises.CompatCompression` used for `exer:regular-compression` and
`exer:polyregular-marked-squaring-compression`: from a grammar compression of `w` with `n` rules
one builds a compression of `w^|w|` with at most `6n` rules, by repeated doubling according to
the binary representation of `|w|` — this is `compatCompression_squaring`.  Since regular
functions are compatible with compression (`compatCompression_of_isRegularFun`) and
compatibility is preserved by composition, every function of the smaller class is compatible
with compression.  Marked squaring is polyregular but not compatible with compression
(`markedSquare_not_compatible_with_compression`), so it is not in the smaller class; and every
function of the smaller class is polyregular, because unmarked squaring is marked squaring
followed by the letter-to-letter map that forgets the underlines.

The exercise itself is `Transducers.Exercises.unmarkedPolyregular_strict_subset_polyregular`.
The one divergence from the book is the one already made for the two compression exercises:
compatibility with compression is taken in the size sense of `CompatCompression`, polynomial
running time not being modelled by this project.  Since a polynomial-time algorithm producing a
compression in particular produces one of polynomial size, this is the weaker hypothesis on the
smaller class and the stronger requirement on marked squaring, so the strictness proved here is
the stronger statement of the two.
-/

namespace Transducers
namespace Exercises

variable {A B C : Type}

/-! ## Powers of a string -/

/-- The concatenation of `m` copies of `u`. -/
def listPow (u : List B) : ℕ → List B
  | 0 => []
  | m + 1 => u ++ listPow u m

@[simp] lemma listPow_zero (u : List B) : listPow u 0 = [] := rfl

@[simp] lemma listPow_one (u : List B) : listPow u 1 = u := by simp [listPow]

lemma listPow_add (u : List B) (a b : ℕ) :
    listPow u (a + b) = listPow u a ++ listPow u b := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by ring, listPow, listPow, ih, List.append_assoc]

/-- **Unmarked squaring** (`exer:squaring-continuous`): the input is repeated as many times as
it has letters. -/
def squaring (w : List A) : List A := listPow w w.length

/-! ## The value of a rule is at most exponentially long -/

lemma length_slpVal_le (rs : List (Rule A)) (i : ℕ) : (slpVal rs i).length ≤ 2 ^ i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match hm : rs[i]? with
    | none => rw [slpVal, hm]; simp
    | some (Rule.letter a) =>
        rw [slpVal_letter hm]
        simpa using Nat.one_le_two_pow
    | some (Rule.cat j k) =>
        by_cases hjk : j < i ∧ k < i
        · rw [slpVal_cat hm hjk.1 hjk.2, List.length_append]
          have h1 : (slpVal rs j).length ≤ 2 ^ (i - 1) :=
            (ih j hjk.1).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
          have h2 : (slpVal rs k).length ≤ 2 ^ (i - 1) :=
            (ih k hjk.2).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
          have hi : 1 ≤ i := by omega
          have : 2 ^ (i - 1) + 2 ^ (i - 1) = 2 ^ i := by
            rw [← two_mul, ← pow_succ']
            congr 1
            omega
          omega
        · rw [slpVal, hm]
          simp [hjk]

/-! ## Building a compression of a power by repeated doubling -/

/-- From a rule with value `u`, one obtains a rule with value `u^m` by adding at most `2N`
rules, where `m ≤ 2^N`: this is the binary method, one doubling and at most one extra
concatenation per bit of `m`. -/
lemma exists_ext_listPow (u : List B) :
    ∀ (N m : ℕ), 0 < m → m ≤ 2 ^ N →
      ∀ (b : List (Rule B)) (r : ℕ), r < b.length → slpVal b r = u →
        ∃ (b' : List (Rule B)) (r' : ℕ), Ext b b' ∧ b'.length ≤ b.length + 2 * N ∧
          r' < b'.length ∧ slpVal b' r' = listPow u m := by
  intro N
  induction N with
  | zero =>
      intro m hm hle b r hr hval
      have hm1 : m = 1 := by simp at hle; omega
      subst hm1
      exact ⟨b, r, Ext.rfl' b, by omega, hr, by rw [hval, listPow_one]⟩
  | succ N ih =>
      intro m hm hle b r hr hval
      by_cases h1 : m = 1
      · subst h1
        exact ⟨b, r, Ext.rfl' b, by omega, hr, by rw [hval, listPow_one]⟩
      · have hm2 : 2 ≤ m := by omega
        have hq : 0 < m / 2 := by omega
        have hq2 : m / 2 ≤ 2 ^ N := by
          rw [pow_succ] at hle
          omega
        obtain ⟨b₁, r₁, e₁, l₁, hlt₁, hv₁⟩ := ih (m / 2) hq hq2 b r hr hval
        obtain ⟨b₂, e₂, l₂, hv₂⟩ := exists_ext_cat b₁ hlt₁ hlt₁
        have hb₁lt : b₁.length < b₂.length := by omega
        have hv₂' : slpVal b₂ b₁.length = listPow u (m / 2 + m / 2) := by
          rw [hv₂, hv₁, listPow_add]
        by_cases hpar : m % 2 = 0
        · refine ⟨b₂, b₁.length, e₁.trans' e₂, by omega, hb₁lt, ?_⟩
          rw [hv₂', show m / 2 + m / 2 = m by omega]
        · have hrlt : r < b₂.length := lt_of_lt_of_le hr (le_trans e₁.length_le e₂.length_le)
          have hvr : slpVal b₂ r = u := by
            rw [(e₁.trans' e₂).val_eq hr, hval]
          obtain ⟨b₃, e₃, l₃, hv₃⟩ := exists_ext_cat b₂ hb₁lt hrlt
          refine ⟨b₃, b₂.length, (e₁.trans' e₂).trans' e₃, by omega, by omega, ?_⟩
          have hcat : ∀ c : ℕ, listPow u c ++ u = listPow u (c + 1) := by
            intro c
            rw [listPow_add, listPow_one]
          rw [hv₃, hv₂', hvr, hcat, show m / 2 + m / 2 + 1 = m by omega]

/-! ## Unmarked squaring is compatible with compression -/

/-- **The size half of the solution of `exer:polyregular-unmarked-squaring`.**  Unmarked
squaring is compatible with compression: a compression of `w` with `n` rules yields a
compression of `w^|w|` with at most `6n` rules. -/
theorem compatCompression_squaring : CompatCompression (squaring : List A → List A) := by
  refine ⟨6, 1, fun rs w hw => ?_⟩
  have hn : 1 ≤ rs.length := List.length_pos_iff.2 hw.1
  by_cases hw0 : w = []
  · subst hw0
    exact ⟨epsSLP, by simpa [squaring] using generates_epsSLP, by simp [epsSLP]; omega⟩
  · have hm : 0 < w.length := List.length_pos_iff.2 hw0
    have hmle : w.length ≤ 2 ^ rs.length := by
      have := length_slpVal_le rs (rs.length - 1)
      rw [hw.2] at this
      exact this.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have heps : slpVal (epsSLP : List (Rule A)) 0 = [] := by
      have := generates_epsSLP (A := A)
      simpa [epsSLP] using this.2
    obtain ⟨b₁, r₁, e₁, l₁, hlt₁, hv₁⟩ := exists_ext_graft (epsSLP : List (Rule A)) hw
    obtain ⟨b₂, r₂, e₂, l₂, hlt₂, hv₂⟩ :=
      exists_ext_listPow w rs.length w.length hm hmle b₁ r₁ hlt₁ hv₁
    have hpos : 0 < b₂.length := by omega
    have heps₂ : slpVal b₂ 0 = [] := by
      rw [(e₁.trans' e₂).val_eq (by simp [epsSLP]), heps]
    have hbuild : BuildSt b₂ r₂ (squaring w) := ⟨hpos, heps₂, hlt₂, hv₂⟩
    obtain ⟨ss, hss, hlen⟩ := generates_of_buildSt hbuild
    refine ⟨ss, hss, ?_⟩
    simp only [epsSLP, List.length_singleton] at l₁
    simp only [pow_one]
    omega

/-! ## Unmarked squaring is polyregular -/

lemma flatten_map_const_eq_listPow (u : List B) (m : ℕ) :
    ((List.range m).map (fun _ => u)).flatten = listPow u m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ]
      simp only [List.map_append, List.flatten_append, ih, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [show m + 1 = m + 1 from rfl, listPow_add, listPow_one]

/-- Forgetting the underlining turns marked squaring into unmarked squaring. -/
lemma map_markedSquare_eq_squaring (w : List A) :
    (markedSquare A w).map (Sum.elim id id) = squaring w := by
  rw [markedSquare, List.map_flatten, List.map_map]
  rw [show ((fun l : List (A ⊕ A) => l.map (Sum.elim id id)) ∘
        fun i => (w.take (i + 1)).map Sum.inl ++ (w.drop (i + 1)).map Sum.inr)
      = fun _ : ℕ => w from ?_]
  · exact flatten_map_const_eq_listPow w w.length
  · funext i
    simp [Function.comp_def, List.map_append, List.map_map, Function.comp_def]

/-- **Unmarked squaring is polyregular**: it is marked squaring followed by the letter-to-letter
map that forgets the underlines. -/
lemma isPolyregular_squaring (A : Type) [Finite A] : IsPolyregular (squaring : List A → List A) :=
  (isPolyregular_markedSquare A).comp' (IsPolyregular.of_regular (isRegularFun_map
      (Sum.elim id id : A ⊕ A → A)))
    (fun w => (map_markedSquare_eq_squaring w).symm)

/-! ## The class obtained by replacing marked squaring with unmarked squaring -/

/-- The family of primes of the smaller class: regular functions and *unmarked* squaring. -/
def UnmarkedFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  IsRegularFun f ∨
  (∃ (A₀ : Type) (e : A ≃ A₀) (e' : B ≃ A₀), ∀ w, f w = (squaring (w.map e)).map e'.symm)

/-- The class of Exercise `exer:polyregular-unmarked-squaring`: finite compositions of regular
functions and of the unmarked squaring `w ↦ w^|w|`. -/
def IsUnmarkedPolyregular {A B : Type} (f : List A → List B) : Prop :=
  CompClosure UnmarkedFam A B f

lemma IsUnmarkedPolyregular.congr {f g : List A → List B} (hf : IsUnmarkedPolyregular f)
    (h : ∀ w, f w = g w) : IsUnmarkedPolyregular g := by
  have : f = g := funext h
  exact this ▸ hf

/-- Every regular function belongs to the smaller class. -/
lemma IsUnmarkedPolyregular.of_regular {f : List A → List B} (hf : IsRegularFun f) :
    IsUnmarkedPolyregular f := CompClosure.base (Or.inl hf)

/-- Unmarked squaring belongs to the smaller class. -/
lemma isUnmarkedPolyregular_squaring (A : Type) :
    IsUnmarkedPolyregular (squaring : List A → List A) :=
  CompClosure.base (Or.inr ⟨A, Equiv.refl _, Equiv.refl _, by intro w; simp⟩)

/-! ## The smaller class is contained in the polyregular functions -/

theorem isPolyregular_of_isUnmarkedPolyregular_aux {A B : Type} {f : List A → List B}
    (hf : IsUnmarkedPolyregular f) : Finite A → Finite B → IsPolyregular f := by
  induction hf with
  | base h =>
      intro hA hB
      rcases h with hreg | ⟨A₀, e, e', hfe⟩
      · exact IsPolyregular.of_regular hreg
      · haveI := hA
        haveI := hB
        haveI : Finite A₀ := Finite.of_equiv _ e
        exact ((IsPolyregular.of_regular (isRegularFun_map ⇑e)).comp'
            (isPolyregular_squaring A₀) (fun _ => rfl)).comp'
          (IsPolyregular.of_regular (isRegularFun_map ⇑e'.symm)) hfe
  | id A => intro _ _; exact isPolyregular_id
  | comp _ _ ihf ihg =>
      intro hA hC
      exact (ihf hA ‹Finite _›).comp (ihg ‹Finite _› hC)

/-- **Every function of the smaller class is polyregular.** -/
theorem isPolyregular_of_isUnmarkedPolyregular {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsUnmarkedPolyregular f) : IsPolyregular f :=
  isPolyregular_of_isUnmarkedPolyregular_aux hf ‹_› ‹_›

/-! ## Every function of the smaller class is compatible with compression -/

theorem compatCompression_of_isUnmarkedPolyregular_aux {A B : Type} {f : List A → List B}
    (hf : IsUnmarkedPolyregular f) : Finite A → Finite B → CompatCompression f := by
  induction hf with
  | base h =>
      intro hA hB
      rcases h with hreg | ⟨A₀, e, e', hfe⟩
      · exact compatCompression_of_isRegularFun_aux hreg hA hB
      · exact (((compatCompression_map ⇑e).comp
          (compatCompression_squaring (A := A₀))).comp
          (compatCompression_map ⇑e'.symm)).congr (fun w => (hfe w).symm)
  | id A => intro _ _; exact compatCompression_id
  | comp _ _ ihf ihg =>
      intro hA hC
      exact (ihf hA ‹Finite _›).comp (ihg ‹Finite _› hC)

/-- **Every function of the smaller class is compatible with compression.** -/
theorem compatCompression_of_isUnmarkedPolyregular {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsUnmarkedPolyregular f) : CompatCompression f :=
  compatCompression_of_isUnmarkedPolyregular_aux hf ‹_› ‹_›

/-! ## Marked squaring is not in the smaller class -/

/-- A polynomial is eventually smaller than an exponential: an `n` above any prescribed bound
with `C * n ^ K < 2 ^ n`. -/
lemma exists_mul_pow_lt_two_pow (C K N : ℕ) : ∃ n : ℕ, N ≤ n ∧ C * n ^ K < 2 ^ n := by
  have h : Filter.Tendsto (fun n : ℕ => ((n : ℝ) ^ K / 2 ^ n)) Filter.atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt K one_lt_two
  have hpos : (0:ℝ) < 1 / ((C : ℝ) + 1) := by positivity
  have h1 : ∀ᶠ n : ℕ in Filter.atTop, ((n : ℝ) ^ K / 2 ^ n) < 1 / ((C : ℝ) + 1) :=
    h.eventually (gt_mem_nhds hpos)
  obtain ⟨n, hn1, hn2⟩ := ((Filter.eventually_ge_atTop N).and h1).exists
  refine ⟨n, hn1, ?_⟩
  have hp : (0:ℝ) < 2 ^ n := by positivity
  rw [div_lt_div_iff₀ hp (by positivity)] at hn2
  have h3 : ((C:ℝ)) * (n:ℝ)^K < 2^n := by nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) n) K]
  exact_mod_cast h3

/-- An exponential eventually overtakes a polynomial. -/
lemma exists_lt_two_pow_sub_one (C k : ℕ) : ∃ n : ℕ, C * (n + 1) ^ k < 2 ^ n - 1 := by
  obtain ⟨n, hn, hlt⟩ := exists_mul_pow_lt_two_pow (C + 2) (2 * k + 2) 2
  refine ⟨n, ?_⟩
  have h1 : (n + 1) ^ k ≤ n ^ (2 * k) := by
    calc (n + 1) ^ k ≤ (n ^ 2) ^ k := Nat.pow_le_pow_left (by nlinarith) k
      _ = n ^ (2 * k) := by rw [← pow_mul, Nat.mul_comm]
  have h2 : n ^ (2 * k) ≤ n ^ (2 * k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 1 ≤ n ^ (2 * k + 2) := Nat.one_le_pow _ _ (by omega)
  have h4 : C * (n + 1) ^ k + 1 ≤ (C + 2) * n ^ (2 * k + 2) := by
    have : C * (n + 1) ^ k ≤ C * n ^ (2 * k + 2) := Nat.mul_le_mul_left C (h1.trans h2)
    nlinarith
  omega

/-- Marked squaring is not compatible with compression, in the form used here: no constants `C`
and `k` bound the size of a compression of the marked square by `C * n ^ k`. -/
theorem not_compatCompression_markedSquare :
    ¬ CompatCompression (markedSquare Unit) := by
  rintro ⟨C, k, hC⟩
  obtain ⟨n, hn⟩ := exists_lt_two_pow_sub_one C k
  obtain ⟨w, ⟨rs, hrs, hgen⟩, hbig⟩ := markedSquare_not_compatible_with_compression n
  obtain ⟨rs', hgen', hlen⟩ := hC rs w hgen
  have h1 : 2 ^ n - 1 ≤ rs'.length := hbig rs' hgen'
  rw [hrs] at hlen
  omega

/-- **Marked squaring is not in the class generated by unmarked squaring.** -/
theorem not_isUnmarkedPolyregular_markedSquare :
    ¬ IsUnmarkedPolyregular (markedSquare Unit) := fun h =>
  not_compatCompression_markedSquare (compatCompression_of_isUnmarkedPolyregular h)

/-! ## The exercise -/

/-- **Exercise `exer:polyregular-unmarked-squaring`.**  If, in Definition
`def:polyregular-functions`, marked squaring is replaced by the unmarked squaring
`w ↦ w^|w|` of `exer:squaring-continuous`, then the resulting class is a *strict* subset of the
polyregular functions: every function of the smaller class is polyregular, and marked squaring
itself is polyregular but not in the smaller class.

The argument is the author's, with one divergence, which is the one already made for
`exer:regular-compression` and `exer:polyregular-marked-squaring-compression`: compatibility with
compression is taken in the *size* sense of `Transducers.Exercises.CompatCompression` — the image
of a string with a compression of `n` rules has a compression of at most `C * n ^ k` rules — and
not in the sense of polynomial running time, which this project does not model.  This is the
weaker statement of the two, so the conclusion is the stronger one: marked squaring is excluded
from the smaller class already because no *bound* of that kind holds for it. -/
theorem unmarkedPolyregular_strict_subset_polyregular :
    (∀ (A B : Type), Finite A → Finite B → ∀ f : List A → List B,
        IsUnmarkedPolyregular f → IsPolyregular f) ∧
      IsPolyregular (markedSquare Unit) ∧ ¬ IsUnmarkedPolyregular (markedSquare Unit) :=
  ⟨fun _ _ hA hB _ hf => isPolyregular_of_isUnmarkedPolyregular_aux hf hA hB,
    isPolyregular_markedSquare Unit, not_isUnmarkedPolyregular_markedSquare⟩

end Exercises
end Transducers
