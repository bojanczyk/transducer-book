/-
Why Definition C.4.7 needs its two requirements.

Definition C.4.7 of *Transducers* (M. Bojańczyk) asks that, in an mso
transduction, every selected element satisfy exactly one letter formula and that
the order formula define a linear order on the selected elements.  The first
formalisation of `RequestProject/PartC/MSODef.lean` dropped these two
requirements; this file shows that they cannot be dropped, i.e. that
Theorem C.4.8 fails for the resulting weaker notion
(`Transducers.IsWeakMSOTransduction`).

The counterexample is the transduction over the alphabet `Bool` whose universe,
letter and order formulas are all "true": every position is selected, every
selected position may carry any letter, and any two selected positions are
comparable in both directions.  Its outputs on an input `w` are therefore *all*
the strings of length `|w|`, so *every* length preserving function is a weak mso
transduction -- in particular the function that maps `w` to the constant string
of length `|w|` saying whether `w` belongs to the (non-regular) language
`{0ⁿ1ⁿ : n ≥ 1}`.  That function is not continuous, hence not regular.
-/
import RequestProject.PartC.MSODef
import RequestProject.PartC.RegAut

namespace Transducers
namespace MSOWeak

open List

/-! ## A non-regular language over `Bool` -/

/-- The language `{0ⁿ1ⁿ : n ≥ 1}`. -/
def sqLang : Language Bool :=
  {w | ∃ n : ℕ, 1 ≤ n ∧ w = List.replicate n false ++ List.replicate n true}

lemma count_false_block (m n : ℕ) :
    (List.replicate m false ++ List.replicate n true).count false = m := by
  simp [List.count_append, List.count_replicate]

lemma count_true_block (m n : ℕ) :
    (List.replicate m false ++ List.replicate n true).count true = n := by
  simp [List.count_append, List.count_replicate]

lemma mem_sqLang_iff (m n : ℕ) :
    (List.replicate m false ++ List.replicate n true) ∈ sqLang ↔ (m = n ∧ 1 ≤ n) := by
  constructor
  · rintro ⟨k, hk, he⟩
    have h1 : m = k := by
      have h : (List.replicate m false ++ List.replicate n true).count false
          = (List.replicate k false ++ List.replicate k true).count false := by rw [he]
      rwa [count_false_block, count_false_block] at h
    have h2 : n = k := by
      have h : (List.replicate m false ++ List.replicate n true).count true
          = (List.replicate k false ++ List.replicate k true).count true := by rw [he]
      rwa [count_true_block, count_true_block] at h
    exact ⟨by omega, by omega⟩
  · rintro ⟨rfl, hn⟩
    exact ⟨m, hn, rfl⟩

lemma not_isRegular_sqLang : ¬ sqLang.IsRegular := by
  intro h
  rw [Language.isRegular_iff_finite_range_leftQuotient] at h
  have hinj : Function.Injective
      (fun n : ℕ => sqLang.leftQuotient (List.replicate (n + 1) false)) := by
    intro n m hnm
    dsimp only at hnm
    have hmem : (List.replicate (n + 1) true) ∈
        sqLang.leftQuotient (List.replicate (n + 1) false) := by
      rw [Language.mem_leftQuotient]
      exact (mem_sqLang_iff (n + 1) (n + 1)).2 ⟨rfl, by omega⟩
    rw [hnm, Language.mem_leftQuotient] at hmem
    have := (mem_sqLang_iff (m + 1) (n + 1)).1 hmem
    omega
  refine (Set.infinite_range_of_injective hinj) (h.subset ?_)
  rintro _ ⟨n, rfl⟩
  exact ⟨List.replicate (n + 1) false, rfl⟩

/-! ## The weak mso transduction that outputs every string of the right length -/

variable {A B : Type}

/-- A formula that holds in every string under every valuation. -/
def trueF : MSO A := MSO.le 0 0

lemma sat_trueF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    MSO.Sat w fo so (trueF : MSO A) := le_refl _

/-- The transduction with one copy, no extra elements, and all formulas true. -/
@[reducible] def allT (A B : Type) : MSOTransduction A B where
  copies := 1
  extra := 0
  univP := fun _ => trueF
  univC := fun _ => trueF
  labP := fun _ _ => trueF
  labC := fun _ _ => trueF
  ordPP := fun _ _ => trueF
  ordPC := fun _ _ => trueF
  ordCP := fun _ _ => trueF
  ordCC := fun _ _ => trueF

lemma allT_selected (w : List A) (x : (allT A B).Elt) :
    (allT A B).selected w x ↔ ∃ p : ℕ, p < w.length ∧ x = Sum.inl (0, p) := by
  cases x with
  | inl ip =>
      obtain ⟨i, p⟩ := ip
      obtain rfl : i = 0 := Subsingleton.elim _ _
      constructor
      · rintro ⟨hp, -⟩
        exact ⟨p, hp, rfl⟩
      · rintro ⟨p', hp', he⟩
        obtain rfl : p = p' := congrArg Prod.snd (Sum.inl.inj he)
        exact ⟨hp', sat_trueF _ _ _⟩
  | inr j => exact absurd j.isLt (Nat.not_lt_zero _)

lemma allT_ordRel (w : List A) (x y : (allT A B).Elt) : (allT A B).ordRel w x y := by
  rcases x with ⟨i, p⟩ | j <;> rcases y with ⟨i', p'⟩ | j' <;> exact le_refl _

lemma allT_labRel (w : List A) (x : (allT A B).Elt) (b : B) : (allT A B).labRel w x b := by
  rcases x with ⟨i, p⟩ | j <;> exact le_refl _

/-- Every function that preserves lengths is a weak mso transduction. -/
theorem isWeakMSOTransduction_of_lengthPreserving {f : List A → List B}
    (hf : ∀ w, (f w).length = w.length) : IsWeakMSOTransduction f := by
  refine ⟨allT A B, fun w => ?_⟩
  refine ⟨(List.range w.length).map (fun p => Sum.inl (0, p)), ?_, ?_, ?_, ?_, ?_⟩
  · refine List.Nodup.map ?_ (List.nodup_range)
    intro p q h
    exact congrArg Prod.snd (Sum.inl.inj h)
  · intro x
    rw [allT_selected]
    constructor
    · intro hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact ⟨p, List.mem_range.1 hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩
  · intro i j hi hj hij
    exact allT_ordRel _ _ _
  · simp [hf w]
  · intro i hi hi'
    exact allT_labRel _ _ _

/-! ## The counterexample -/

open scoped Classical in
/-- The function that maps `w` to the string of length `|w|` all of whose
letters say whether `w` belongs to `{0ⁿ1ⁿ : n ≥ 1}`. -/
noncomputable def badFun : List Bool → List Bool :=
  fun w => List.replicate w.length (decide (w ∈ sqLang))

lemma badFun_length (w : List Bool) : (badFun w).length = w.length := by
  simp [badFun]

/-- The language of strings containing the letter `true`. -/
def someTrue : Language Bool := {v | true ∈ v}

lemma foldl_or_eq_true (v : List Bool) (s : Bool) :
    v.foldl (fun s a => s || a) s = true ↔ (s = true ∨ true ∈ v) := by
  induction v generalizing s with
  | nil => simp
  | cons a v ih =>
      rw [List.foldl_cons, ih]
      cases a <;> cases s <;> simp

lemma isRegular_someTrue : someTrue.IsRegular := by
  have h := RegAut.isRegular_foldl (Γ := Bool) (fun (s : Bool) (a : Bool) => s || a) false {true}
  refine RegAut.isRegular_of_eq h (fun u => ?_)
  show true ∈ u ↔ u.foldl (fun s a => s || a) false ∈ ({true} : Set Bool)
  rw [Set.mem_singleton_iff, foldl_or_eq_true]
  simp

open scoped Classical in
lemma not_isRegularFun_badFun : ¬ IsRegularFun badFun := by
  intro h
  have hc := continuous_of_isRegularFun h someTrue isRegular_someTrue
  refine not_isRegular_sqLang (RegAut.isRegular_of_eq hc (fun u => ?_))
  show u ∈ sqLang ↔ true ∈ List.replicate u.length (decide (u ∈ sqLang))
  constructor
  · intro hu
    have hlen : 0 < u.length := by
      obtain ⟨n, hn, rfl⟩ := hu
      simp
      omega
    rw [decide_eq_true hu]
    exact List.mem_replicate.2 ⟨by omega, rfl⟩
  · intro hu
    have hd := List.eq_of_mem_replicate hu
    by_contra hns
    rw [decide_eq_false hns] at hd
    exact Bool.noConfusion hd

/-- **The requirements of Definition C.4.7 cannot be dropped.**  There is a
function which is a *weak* mso transduction (an mso transduction in which the
letter formulas need not be exclusive and the order formula need not define a
linear order) and which is not regular. -/
theorem exists_weakMSOTransduction_not_regular :
    ∃ f : List Bool → List Bool, IsWeakMSOTransduction f ∧ ¬ IsRegularFun f :=
  ⟨badFun, isWeakMSOTransduction_of_lengthPreserving badFun_length,
    not_isRegularFun_badFun⟩

end MSOWeak

export MSOWeak (exists_weakMSOTransduction_not_regular)

end Transducers
