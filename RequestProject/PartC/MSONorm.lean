/-
Normalisation of the type `τ` of an mso transduction: **Lemma `lem:logic-reduction-to-type-n`** of
*Transducers* (M. Bojańczyk).

Definition `def:mso-transduction` presents the output universe of an mso transduction by a *linear*
type `τ = k · n + c`: `k` copies of the positions of the input string and `c` extra elements, with
separate families of formulas for the two kinds of elements.  Lemma `lem:logic-reduction-to-type-n`
of the book removes the extra elements by padding the input string; here we do the same thing
without changing the input, by attaching each extra element to the *first* position of the input
string.  The result is a *normalised* transduction (`NormT` below): a single finite set of tags, a
universe formula and a family of letter formulas with one free first-order variable for every tag,
and an order formula with two free first-order variables for every pair of tags.

The empty input string has no first position, so the normalisation is only
claimed for non-empty inputs; the value of the transduction on the empty input
is a fixed string, and is dealt with separately in
`RequestProject/PartC/MSOReg.lean`.
-/
import RequestProject.PartC.MSOSubst

namespace Transducers

/-- A *normalised* mso transduction: the elements of the output universe are
pairs (tag, position), the universe and letter formulas have the single free
variable `x₀`, and the order formulas have the two free variables `x₀, x₁`. -/
structure NormT (A B : Type) where
  /-- The (finite) set of tags. -/
  Tag : Type
  /-- Finiteness of the set of tags. -/
  finTag : Finite Tag
  /-- The universe formula of a tag; free variable `x₀`. -/
  U : Tag → MSO A
  /-- The letter formulas of a tag; free variable `x₀`. -/
  Lb : Tag → B → MSO A
  /-- The order formula of a pair of tags; free variables `x₀, x₁`. -/
  Ord : Tag → Tag → MSO A

namespace NormT

variable {A B : Type}

/-- An element of the output universe, before selection. -/
abbrev Elt (N : NormT A B) : Type := N.Tag × ℕ

/-- The elements selected by the universe formulas. -/
def sel (N : NormT A B) (w : List A) (x : N.Elt) : Prop :=
  x.2 < w.length ∧ MSO.Sat w (fun _ => x.2) (fun _ => ∅) (N.U x.1)

/-- The order defined by the order formulas. -/
def ord (N : NormT A B) (w : List A) (x y : N.Elt) : Prop :=
  MSO.Sat w (fun v => if v = 0 then x.2 else y.2) (fun _ => ∅) (N.Ord x.1 y.1)

/-- The labelling defined by the letter formulas. -/
def lab (N : NormT A B) (w : List A) (x : N.Elt) (b : B) : Prop :=
  MSO.Sat w (fun _ => x.2) (fun _ => ∅) (N.Lb x.1 b)

/-- The list `es` enumerates the selected elements in the order given by the
order formulas, and the string `v` is the corresponding sequence of letters. -/
def Presents (N : NormT A B) (w : List A) (es : List N.Elt) (v : List B) : Prop :=
  es.Nodup ∧ (∀ x, x ∈ es ↔ N.sel w x) ∧
  (∀ (i j : ℕ) (hi : i < es.length) (hj : j < es.length), i < j → N.ord w es[i] es[j]) ∧
  es.length = v.length ∧
  ∀ (i : ℕ) (hi : i < es.length) (hi' : i < v.length), N.lab w es[i] v[i]

/-- The requirements of Definition `def:mso-transduction`, for a normalised transduction: on the
selected elements the letter formulas are exclusive and the order formula is a
linear order (transitivity is not needed below and is therefore omitted). -/
def Proper (N : NormT A B) (w : List A) : Prop :=
  (∀ x b b', N.sel w x → N.lab w x b → N.lab w x b' → b = b') ∧
  (∀ x, N.sel w x → N.ord w x x) ∧
  (∀ x y, N.sel w x → N.sel w y → N.ord w x y → N.ord w y x → x = y) ∧
  (∀ x y, N.sel w x → N.sel w y → N.ord w x y ∨ N.ord w y x)

end NormT

/-! ## The normalisation -/

namespace MSOTransduction

variable {A B : Type}

/-- "The variable `x₀` denotes the first position of the string." -/
def isFirstF (A : Type) : MSO A := MSO.not (MSO.exFO 1 (MSO.not (MSO.le 0 1)))

lemma sat_isFirstF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (hw : 0 < w.length) :
    MSO.Sat w fo so (isFirstF A) ↔ fo 0 = 0 := by
  simp only [isFirstF, MSO.Sat, not_exists, not_and, not_not, Function.update_of_ne,
    Nat.zero_ne_one, ne_eq, not_false_eq_true]
  constructor
  · intro h
    have := h 0 hw
    simp only [Function.update_self] at this
    omega
  · intro h p hp
    simp only [Function.update_self, h]
    exact Nat.zero_le _

/-- The tags of the normalised transduction: the copies of the positions and
the extra elements. -/
abbrev NTag (T : MSOTransduction A B) : Type := Fin T.copies ⊕ Fin T.extra

/-- The universe formulas of the normalised transduction. -/
def normU (T : MSOTransduction A B) : T.NTag → MSO A
  | Sum.inl i => T.univP i
  | Sum.inr j => MSO.and (isFirstF A) (MSO.atv 0 (T.univC j))

/-- The letter formulas of the normalised transduction. -/
def normLb (T : MSOTransduction A B) : T.NTag → B → MSO A
  | Sum.inl i, b => T.labP i b
  | Sum.inr j, b => MSO.atv 0 (T.labC j b)

/-- The order formulas of the normalised transduction. -/
def normOrd (T : MSOTransduction A B) : T.NTag → T.NTag → MSO A
  | Sum.inl i, Sum.inl i' => T.ordPP i i'
  | Sum.inl i, Sum.inr j => MSO.atv 0 (T.ordPC i j)
  | Sum.inr j, Sum.inl i => MSO.atv 1 (T.ordCP j i)
  | Sum.inr j, Sum.inr j' => MSO.atv 0 (T.ordCC j j')

/-- The normalised transduction attached to an mso transduction. -/
def norm (T : MSOTransduction A B) : NormT A B where
  Tag := T.NTag
  finTag := inferInstance
  U := T.normU
  Lb := T.normLb
  Ord := T.normOrd

@[simp] lemma norm_Tag (T : MSOTransduction A B) : T.norm.Tag = T.NTag := rfl

/-- The map from the elements of `τ = k · n + c` to the elements of the
normalised transduction: an extra element is attached to the first position. -/
def normElt (T : MSOTransduction A B) : T.Elt → T.norm.Elt
  | Sum.inl (i, p) => (Sum.inl i, p)
  | Sum.inr j => (Sum.inr j, 0)

lemma normElt_injective (T : MSOTransduction A B) : Function.Injective T.normElt := by
  rintro (⟨i, p⟩ | j) (⟨i', p'⟩ | j') h <;> simp [normElt] at h ⊢ <;> tauto

lemma sat_norm_sel (T : MSOTransduction A B) {w : List A} (hw : 0 < w.length)
    (y : T.Elt) : T.norm.sel w (T.normElt y) ↔ T.selected w y := by
  rcases y with ⟨i, p⟩ | j
  · simp only [normElt, NormT.sel, norm, normU, selected]
  · simp only [normElt, NormT.sel, norm, normU, selected, MSO.Sat]
    constructor
    · rintro ⟨-, -, h⟩
      rwa [MSO.sat_atv w 0 _ _ _ hw] at h
    · intro h
      refine ⟨hw, ?_, ?_⟩
      · rw [sat_isFirstF w _ _ hw]
      · rw [MSO.sat_atv w 0 _ _ _ hw]; exact h

lemma norm_pos_lt (T : MSOTransduction A B) {w : List A} (hw : 0 < w.length)
    {y : T.Elt} (hy : T.selected w y) : (T.normElt y).2 < w.length := by
  rcases y with ⟨i, p⟩ | j
  · exact hy.1
  · exact hw

lemma sat_norm_ord (T : MSOTransduction A B) {w : List A} (hw : 0 < w.length)
    {y y' : T.Elt} (hy : T.selected w y) (hy' : T.selected w y') :
    T.norm.ord w (T.normElt y) (T.normElt y') ↔ T.ordRel w y y' := by
  have h1 := T.norm_pos_lt hw hy
  have h2 := T.norm_pos_lt hw hy'
  rcases y with ⟨i, p⟩ | j <;> rcases y' with ⟨i', p'⟩ | j'
  · simp only [normElt, NormT.ord, norm, normOrd, ordRel]
  · simp only [normElt, NormT.ord, norm, normOrd, ordRel]
    rw [MSO.sat_atv w 0 _ _ _ (by simpa using h1)]
    simp
  · simp only [normElt, NormT.ord, norm, normOrd, ordRel]
    rw [MSO.sat_atv w 1 _ _ _ (by simpa using h2)]
    simp
  · simp only [normElt, NormT.ord, norm, normOrd, ordRel]
    rw [MSO.sat_atv w 0 _ _ _ (by simpa using hw)]
    simp

lemma sat_norm_lab (T : MSOTransduction A B) {w : List A} (hw : 0 < w.length)
    {y : T.Elt} (hy : T.selected w y) (b : B) :
    T.norm.lab w (T.normElt y) b ↔ T.labRel w y b := by
  rcases y with ⟨i, p⟩ | j
  · simp only [normElt, NormT.lab, norm, normLb, labRel]
  · simp only [normElt, NormT.lab, norm, normLb, labRel]
    rw [MSO.sat_atv w 0 _ _ _ hw]

/-- Every selected element of the normalised transduction comes from an element
of `τ`. -/
lemma exists_normElt (T : MSOTransduction A B) {w : List A} (hw : 0 < w.length)
    {x : T.norm.Elt} (hx : T.norm.sel w x) : ∃ y : T.Elt, T.normElt y = x := by
  obtain ⟨t, p⟩ := x
  rcases t with i | j
  · exact ⟨Sum.inl (i, p), rfl⟩
  · refine ⟨Sum.inr j, ?_⟩
    obtain ⟨-, hsat⟩ := hx
    simp only [norm, normU, MSO.Sat] at hsat
    have : p = 0 := by
      have := (sat_isFirstF w (fun _ => p) (fun _ => ∅) hw).1 hsat.1
      simpa using this
    simp [normElt, this]

/-- **Lemma `lem:logic-reduction-to-type-n` (normalisation of `τ`).**  Every mso transduction
agrees, on non-empty inputs, with a normalised transduction. -/
theorem exists_norm (T : MSOTransduction A B) (hP : T.Proper) :
    ∃ N : NormT A B,
      (∀ w : List A, 0 < w.length → N.Proper w) ∧
      (∀ (w : List A) (v : List B), 0 < w.length → T.Outputs w v →
        ∃ es : List N.Elt, N.Presents w es v) := by
  refine ⟨T.norm, ?_, ?_⟩
  · intro w hw
    obtain ⟨hlab, hrefl, hanti, -, htot⟩ := hP w
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro x b b' hx hb hb'
      obtain ⟨y, rfl⟩ := T.exists_normElt hw hx
      have hy : T.selected w y := (T.sat_norm_sel hw y).1 hx
      obtain ⟨c, -, hc⟩ := hlab y hy
      rw [hc b ((T.sat_norm_lab hw hy b).1 hb), hc b' ((T.sat_norm_lab hw hy b').1 hb')]
    · intro x hx
      obtain ⟨y, rfl⟩ := T.exists_normElt hw hx
      have hy : T.selected w y := (T.sat_norm_sel hw y).1 hx
      exact (T.sat_norm_ord hw hy hy).2 (hrefl y hy)
    · intro x x' hx hx' h h'
      obtain ⟨y, rfl⟩ := T.exists_normElt hw hx
      obtain ⟨y', rfl⟩ := T.exists_normElt hw hx'
      have hy : T.selected w y := (T.sat_norm_sel hw y).1 hx
      have hy' : T.selected w y' := (T.sat_norm_sel hw y').1 hx'
      exact congrArg T.normElt (hanti y y' hy hy'
        ((T.sat_norm_ord hw hy hy').1 h) ((T.sat_norm_ord hw hy' hy).1 h'))
    · intro x x' hx hx'
      obtain ⟨y, rfl⟩ := T.exists_normElt hw hx
      obtain ⟨y', rfl⟩ := T.exists_normElt hw hx'
      have hy : T.selected w y := (T.sat_norm_sel hw y).1 hx
      have hy' : T.selected w y' := (T.sat_norm_sel hw y').1 hx'
      rcases htot y y' hy hy' with h | h
      · exact Or.inl ((T.sat_norm_ord hw hy hy').2 h)
      · exact Or.inr ((T.sat_norm_ord hw hy' hy).2 h)
  · rintro w v hw ⟨es, hnodup, hmem, hsorted, hlen, hlabs⟩
    refine ⟨es.map T.normElt, ?_, ?_, ?_, ?_, ?_⟩
    · exact hnodup.map T.normElt_injective
    · intro x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact (T.sat_norm_sel hw y).2 ((hmem y).1 hy)
      · intro hx
        obtain ⟨y, rfl⟩ := T.exists_normElt hw hx
        exact List.mem_map_of_mem ((hmem y).2 ((T.sat_norm_sel hw y).1 hx))
    · intro i j hi hj hij
      rw [List.length_map] at hi hj
      have hyi : T.selected w es[i] := (hmem _).1 (List.getElem_mem hi)
      have hyj : T.selected w es[j] := (hmem _).1 (List.getElem_mem hj)
      rw [List.getElem_map, List.getElem_map]
      refine (T.sat_norm_ord hw hyi hyj).2 ?_
      simpa using hsorted i j hi hj hij
    · rw [List.length_map]; exact hlen
    · intro i hi hi'
      rw [List.length_map] at hi
      have hyi : T.selected w es[i] := (hmem _).1 (List.getElem_mem hi)
      rw [List.getElem_map]
      refine (T.sat_norm_lab hw hyi _).2 ?_
      simpa using hlabs i hi hi'

end MSOTransduction

end Transducers
