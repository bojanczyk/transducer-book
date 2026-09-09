/-
Part D: the closure properties of the polyregular functions that the combinators of Definition
`def:polyregular-terms` need -- the sum of two polyregular functions, case distinction over a
regular language, and concatenation.

For the regular functions these are Claim `claim:conditional` and Lemma
`lem:regular-closure-properties` (`RequestProject/PartC/RegSum.lean` and
`RequestProject/PartC/RegClosure.lean`), and the arguments here are the same, once the *sum* of two
polyregular functions is available:

    F : (A₁ + A₂)* → (B₁ + B₂)*      F (u coloured by the first summand)  = f₁ u, coloured
                                     F (v coloured by the second summand) = f₂ v, coloured.

The sum of two *regular* functions is Claim `claim:conditional`; for polyregular functions it is
proved here by induction on the definition of a polyregular function as a composition of primes.
The sums compose, the sum of two regular functions is regular, and the only new case is the sum of
marked squaring with the identity, which is again a computation on all the ways of cutting the
input into a prefix and a suffix (`RequestProject/PartD/PolyPerSplit.lean`): the copies in which
the cut falls after the `i`-th letter give the `i`-th copy of the marked square, and on an input
from the *other* summand the same computation is asked to keep, in each copy, only the letter at
the cut, which reproduces the input.

Everything is stated for inputs and outputs that carry a marker `#` in front -- that is, for
strings of the form `# a₁ ⋯ aₙ` over `A + 1` -- because a sum is only well behaved on nonempty
inputs, exactly as in Claim `claim:conditional`; the marker also makes the sums compose.
-/
import RequestProject.PartD.PolyMapLift
import RequestProject.PartC.RegSum

namespace Transducers

/-! ## The sum of a polyregular function with the identity -/

/-- The marked form of a string: a fresh marker, and then the string. -/
def markStr {A : Type} (u : List A) : List (Option A) := none :: u.map some

@[simp] lemma markStr_ne_nil {A : Type} (u : List A) : markStr u ≠ [] := by simp [markStr]

lemma del_markStr {A : Type} (u : List A) : RegCl.del (markStr u) = u :=
  RegCl.del_marked u

/-- `SumLeftPoly A₂ f` says that the sum of `f` with the identity of `A₂` is polyregular: there is
a polyregular function on the coloured strings which computes `f` on the strings coloured by the
first summand and the identity on those coloured by the second one.  All the strings carry the
marker of `Transducers.markStr`. -/
def SumLeftPoly (A₂ : Type) {A₁ B₁ : Type} (f : List A₁ → List B₁) : Prop :=
  ∃ F : List (Option A₁ ⊕ Option A₂) → List (Option B₁ ⊕ Option A₂), IsPolyregular F ∧
    (∀ u : List A₁, F ((markStr u).map Sum.inl) = (markStr (f u)).map Sum.inl) ∧
    (∀ v : List A₂, F ((markStr v).map Sum.inr) = (markStr v).map Sum.inr)

lemma SumLeftPoly.congr {A₁ A₂ B₁ : Type} {f g : List A₁ → List B₁} (h : SumLeftPoly A₂ f)
    (hfg : ∀ u, f u = g u) : SumLeftPoly A₂ g := by
  obtain ⟨F, hF, hL, hR⟩ := h
  exact ⟨F, hF, fun u => by rw [hL u, hfg u], hR⟩

lemma SumLeftPoly.comp {A₁ M B₁ A₂ : Type} [Finite M] [Finite A₂] {f : List A₁ → List M}
    {g : List M → List B₁} (hf : SumLeftPoly A₂ f) (hg : SumLeftPoly A₂ g) :
    SumLeftPoly A₂ (fun u => g (f u)) := by
  obtain ⟨F₁, hF₁, hL₁, hR₁⟩ := hf
  obtain ⟨F₂, hF₂, hL₂, hR₂⟩ := hg
  refine ⟨fun x => F₂ (F₁ x), hF₁.comp' hF₂ (fun _ => rfl), fun u => ?_, fun v => ?_⟩
  · show F₂ (F₁ ((markStr u).map Sum.inl)) = _
    rw [hL₁ u, hL₂ (f u)]
  · show F₂ (F₁ ((markStr v).map Sum.inr)) = _
    rw [hR₁ v, hR₂ v]

lemma sumLeftPoly_id {A₁ A₂ : Type} : SumLeftPoly A₂ (id : List A₁ → List A₁) :=
  ⟨id, isPolyregular_id, fun _ => rfl, fun _ => rfl⟩

lemma sumLeftPoly_of_regular {A₁ B₁ A₂ : Type} [Finite A₁] [Finite B₁] [Finite A₂]
    {f : List A₁ → List B₁} (hf : IsRegularFun f) : SumLeftPoly A₂ f := by
  have hf' : IsRegularFun (fun x : List (Option A₁) => markStr (f (RegCl.del x))) :=
    (RegCl.isRegularFun_del.comp' hf (fun _ => rfl)).comp'
      (IsRegularFun.of_rational (isRationalFun_comp
        (isRationalFun_map (some : B₁ → Option B₁)) (isRationalFun_cons (none : Option B₁))))
      (fun _ => rfl)
  have hg' : IsRegularFun (fun y : List (Option A₂) => markStr (RegCl.del y)) :=
    RegCl.isRegularFun_del.comp'
      (IsRegularFun.of_rational (isRationalFun_comp
        (isRationalFun_map (some : A₂ → Option A₂)) (isRationalFun_cons (none : Option A₂))))
      (fun _ => rfl)
  obtain ⟨bot, F, -, -, hFreg, hFL, hFR, -⟩ := sum_of_regular_aux hf' hg'
  refine ⟨F, IsPolyregular.of_regular hFreg, fun u => ?_, fun v => ?_⟩
  · rw [hFL (markStr u) (markStr_ne_nil u), del_markStr]
  · rw [hFR (markStr v) (markStr_ne_nil v), del_markStr]

/-! ### The sum of marked squaring with the identity

Marked squaring is applied to *every block* of a string by
`Transducers.isPolyregular_mapLift_markedSquare`, and that is enough to compute it on the strings
coloured by the first summand while leaving those coloured by the second one alone: it suffices to
cut the input into blocks in two different ways, depending on the colour.  A letter-to-word
homomorphism can do this, because the colour is carried by every letter:

* a string `# a₁ ⋯ aₙ` coloured by the first summand becomes the two blocks `⟨ | a₁ ⋯ aₙ`, so that
  marked squaring is applied to the whole of `a₁ ⋯ aₙ`;
* a string `# b₁ ⋯ bₙ` coloured by the second summand becomes the blocks `⟩ | b₁ | ⋯ | bₙ | `, one
  letter each, and marked squaring leaves a one-letter block unchanged (up to underlining).

The two extra letters `⟨` and `⟩` in the first block remember the colour, so that a final
homomorphism can put the marker back in front of the right summand. -/

namespace MSSum

variable {A₁ A₂ : Type}

/-- The alphabet used for the sum of marked squaring with the identity: the letters of the two
summands, and two letters remembering which summand the input came from. -/
abbrev Cc (A₁ A₂ : Type) : Type := (A₁ ⊕ A₂) ⊕ Bool

/-- Cutting the input into blocks: the whole of the first summand is one block, while the second
summand is cut into one-letter blocks. -/
def rho : Option A₁ ⊕ Option A₂ → List (Option (Cc A₁ A₂))
  | Sum.inl none => [some (Sum.inr false), none]
  | Sum.inl (some a) => [some (Sum.inl (Sum.inl a))]
  | Sum.inr none => [some (Sum.inr true), none]
  | Sum.inr (some b) => [some (Sum.inl (Sum.inr b)), none]

/-- Reading off the result: the marker of the summand the input came from, the marked square of
the first summand, and the letters of the second summand. -/
def sig : Option (Cc A₁ A₂ ⊕ Cc A₁ A₂) → List (Option (A₁ ⊕ A₁) ⊕ Option A₂)
  | some (Sum.inl (Sum.inr false)) => [Sum.inl none]
  | some (Sum.inl (Sum.inr true)) => [Sum.inr none]
  | some (Sum.inl (Sum.inl (Sum.inl a))) => [Sum.inl (some (Sum.inl a))]
  | some (Sum.inr (Sum.inl (Sum.inl a))) => [Sum.inl (some (Sum.inr a))]
  | some (Sum.inl (Sum.inl (Sum.inr b))) => [Sum.inr (some b)]
  | _ => []

/-- The function witnessing that the sum of marked squaring with the identity is polyregular. -/
def sumMS (x : List (Option A₁ ⊕ Option A₂)) : List (Option (A₁ ⊕ A₁) ⊕ Option A₂) :=
  homOf sig (mapLift (markedSquare (Cc A₁ A₂)) (homOf rho x))

/-- The letters of the second summand, as one-letter blocks, with an empty block at the end. -/
def rBlocks (v : List A₂) : List (List (Cc A₁ A₂)) :=
  v.map (fun b => [Sum.inl (Sum.inr b)]) ++ [[]]

lemma rBlocks_ne_nil (v : List A₂) : (rBlocks (A₁ := A₁) v) ≠ [] := by
  simp [rBlocks]

lemma blockStr_rBlocks (v : List A₂) :
    blockStr (rBlocks (A₁ := A₁) v)
      = (v.map (fun b => [some (Sum.inl (Sum.inr b)), (none : Option (Cc A₁ A₂))])).flatten := by
  induction v with
  | nil => simp [rBlocks]
  | cons b v ih =>
      rw [show rBlocks (A₁ := A₁) (b :: v)
        = [Sum.inl (Sum.inr b)] :: rBlocks (A₁ := A₁) v from rfl,
        blockStr_cons _ _ (rBlocks_ne_nil v), ih]
      simp

lemma homOf_rho_inl (u : List A₁) :
    homOf rho ((markStr u).map (Sum.inl : Option A₁ → Option A₁ ⊕ Option A₂))
      = blockStr [[Sum.inr false], u.map (fun a => Sum.inl (Sum.inl a) : A₁ → Cc A₁ A₂)] := by
  have hu : ∀ u : List A₁, (u.map (fun a => rho (A₂ := A₂) (Sum.inl (some a)))).flatten
      = (u.map (fun a => Sum.inl (Sum.inl a) : A₁ → Cc A₁ A₂)).map some := by
    intro u
    induction u with
    | nil => rfl
    | cons a u ih => simpa [rho] using ih
  rw [markStr]
  simp only [List.map_cons, List.map_map, homOf, List.flatten_cons, Function.comp_def]
  rw [show ((u.map fun a => rho (A₂ := A₂) (Sum.inl (some a)))).flatten
    = (u.map (fun a => Sum.inl (Sum.inl a) : A₁ → Cc A₁ A₂)).map some from hu u]
  rw [blockStr_cons _ _ (by simp)]
  simp [rho]

lemma homOf_rho_inr (v : List A₂) :
    homOf rho ((markStr v).map (Sum.inr : Option A₂ → Option A₁ ⊕ Option A₂))
      = blockStr ([Sum.inr true] :: rBlocks (A₁ := A₁) v) := by
  rw [blockStr_cons _ _ (rBlocks_ne_nil v), blockStr_rBlocks, markStr]
  simp only [List.map_cons, List.map_map, homOf, List.flatten_cons, Function.comp_def]
  rw [show ((v.map fun b => rho (A₁ := A₁) (Sum.inr (some b)))).flatten
    = (v.map (fun b => [some (Sum.inl (Sum.inr b)), (none : Option (Cc A₁ A₂))])).flatten from rfl]
  simp [rho]

lemma homOf_sig_left (z : List (A₁ ⊕ A₁)) :
    homOf sig ((z.map (Sum.map (fun a => Sum.inl (Sum.inl a) : A₁ → Cc A₁ A₂)
        (fun a => Sum.inl (Sum.inl a)))).map some)
      = z.map (fun y => Sum.inl (some y)) := by
  induction z with
  | nil => rfl
  | cons y z ih => cases y <;> simpa [homOf, sig] using ih

end MSSum

open MSSum in
/-- **The sum of marked squaring with the identity is polyregular.** -/
theorem sumLeftPoly_markedSquare (A₀ A₂ : Type) [Finite A₀] [Finite A₂] :
    SumLeftPoly A₂ (markedSquare A₀) := by
  haveI : Finite (Cc A₀ A₂) := inferInstance
  refine ⟨sumMS, ?_, fun u => ?_, fun v => ?_⟩
  · have h1 : IsPolyregular (fun x : List (Option A₀ ⊕ Option A₂) => homOf rho x) :=
      IsPolyregular.of_regular (IsRegularFun.of_rational (isRationalFun_homOf rho))
    have h2 : IsPolyregular (mapLift (markedSquare (Cc A₀ A₂))) :=
      isPolyregular_mapLift_markedSquare (Cc A₀ A₂)
    have h3 : IsPolyregular
        (homOf (sig : Option (Cc A₀ A₂ ⊕ Cc A₀ A₂) → List (Option (A₀ ⊕ A₀) ⊕ Option A₂))) :=
      IsPolyregular.of_regular (IsRegularFun.of_rational (isRationalFun_homOf sig))
    exact ((h1.comp' h2 (fun _ => rfl)).comp' h3 (fun _ => rfl)).congr (fun _ => rfl)
  · show homOf sig (mapLift (markedSquare (Cc A₀ A₂)) (homOf rho _)) = _
    rw [homOf_rho_inl u, mapLift_blockStr _ _ (by simp), homOf_blockStr _ rfl]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]
    rw [markedSquare_singleton, markedSquare_map, homOf_sig_left]
    show homOf sig ([Sum.inl (Sum.inr false)].map some) ++ _ = _
    rw [show homOf (sig (A₁ := A₀) (A₂ := A₂))
      ([Sum.inl (Sum.inr false)].map some) = [Sum.inl none] from rfl]
    simp [markStr, List.map_map, Function.comp_def]
  · show homOf sig (mapLift (markedSquare (Cc A₀ A₂)) (homOf rho _)) = _
    rw [homOf_rho_inr v, mapLift_blockStr _ _ (by simp), homOf_blockStr _ rfl]
    have hv : ∀ v : List A₂,
        (((rBlocks (A₁ := A₀) v).map (markedSquare (Cc A₀ A₂))).map
          (fun b => homOf (sig (A₁ := A₀) (A₂ := A₂)) (b.map some))).flatten
        = v.map (fun b => Sum.inr (some b)) := by
      intro v
      induction v with
      | nil => rfl
      | cons b v ih =>
          rw [show rBlocks (A₁ := A₀) (b :: v)
            = [Sum.inl (Sum.inr b)] :: rBlocks (A₁ := A₀) v from rfl]
          simpa [homOf, sig] using ih
    rw [List.map_cons, List.map_cons, List.flatten_cons, hv, markedSquare_singleton]
    rw [show homOf (sig (A₁ := A₀) (A₂ := A₂))
      (([Sum.inl (Sum.inr true)] : List (Cc A₀ A₂ ⊕ Cc A₀ A₂)).map some)
      = [Sum.inr none] from rfl]
    simp [markStr, List.map_map, Function.comp_def]

/-- **The sum of a polyregular function with the identity is polyregular**, in the form in which
the induction on the composition of primes is carried out. -/
theorem sumLeftPoly_of_isPolyregular_aux {A₁ B₁ : Type} {f : List A₁ → List B₁}
    (hf : IsPolyregular f) :
    Finite A₁ → Finite B₁ → ∀ (A₂ : Type), Finite A₂ → SumLeftPoly A₂ f := by
  induction hf with
  | @base A B f h =>
      intro hA hB A₂ hA₂
      haveI := hA; haveI := hB; haveI := hA₂
      rcases h with hreg | ⟨A₀, e, e', hfe⟩
      · exact sumLeftPoly_of_regular hreg
      · haveI : Finite A₀ := Finite.of_equiv A e
        haveI : Finite (A₀ ⊕ A₀) := inferInstance
        have h1 : SumLeftPoly A₂ (fun w : List A => w.map e) :=
          sumLeftPoly_of_regular (IsRegularFun.of_rational (isRationalFun_map (e : A → A₀)))
        have h3 : SumLeftPoly A₂ (fun u : List (A₀ ⊕ A₀) => u.map e'.symm) :=
          sumLeftPoly_of_regular
            (IsRegularFun.of_rational (isRationalFun_map (e'.symm : A₀ ⊕ A₀ → B)))
        exact (((h1.comp (sumLeftPoly_markedSquare A₀ A₂)).comp h3)).congr
          (fun w => (hfe w).symm)
  | id A => intro _ _ _ _; exact sumLeftPoly_id
  | @comp A M B hM f g _ _ ihf ihg =>
      intro hA hB A₂ hA₂
      haveI := hA; haveI := hB; haveI := hM; haveI := hA₂
      exact ((ihf hA hM A₂ hA₂).comp (ihg hM hB A₂ hA₂)).congr (fun _ => rfl)

/-- **The sum of a polyregular function with the identity is polyregular.** -/
theorem sumLeftPoly_of_isPolyregular {A₁ B₁ A₂ : Type} [Finite A₁] [Finite B₁] [Finite A₂]
    {f : List A₁ → List B₁} (hf : IsPolyregular f) : SumLeftPoly A₂ f :=
  sumLeftPoly_of_isPolyregular_aux hf ‹_› ‹_› A₂ ‹_›

/-! ## The sum of two polyregular functions -/

/-- **The sum of two polyregular functions is polyregular.**  This is the polyregular counterpart
of Claim `claim:conditional`. -/
theorem exists_polySum {A₁ A₂ B₁ B₂ : Type} [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    {f₁ : List A₁ → List B₁} {f₂ : List A₂ → List B₂}
    (hf₁ : IsPolyregular f₁) (hf₂ : IsPolyregular f₂) :
    ∃ F : List (Option A₁ ⊕ Option A₂) → List (Option B₁ ⊕ Option B₂), IsPolyregular F ∧
      (∀ u : List A₁, F ((markStr u).map Sum.inl) = (markStr (f₁ u)).map Sum.inl) ∧
      (∀ v : List A₂, F ((markStr v).map Sum.inr) = (markStr (f₂ v)).map Sum.inr) := by
  -- the sum of `f₂` with the identity of `A₁`, with the two summands exchanged
  obtain ⟨G, hG, hGL, hGR⟩ := sumLeftPoly_of_isPolyregular (A₂ := A₁) hf₂
  obtain ⟨F, hF, hFL, hFR⟩ := sumLeftPoly_of_isPolyregular (A₂ := B₂) hf₁
  have hswap : IsPolyregular (fun x : List (Option A₁ ⊕ Option A₂) => x.map Sum.swap) :=
    IsPolyregular.of_regular (IsRegularFun.of_rational
      (isRationalFun_map (Sum.swap : Option A₁ ⊕ Option A₂ → Option A₂ ⊕ Option A₁)))
  have hswap' : IsPolyregular (fun y : List (Option B₂ ⊕ Option A₁) => y.map Sum.swap) :=
    IsPolyregular.of_regular (IsRegularFun.of_rational
      (isRationalFun_map (Sum.swap : Option B₂ ⊕ Option A₁ → Option A₁ ⊕ Option B₂)))
  refine ⟨fun x => F (((G ((x.map Sum.swap))).map Sum.swap)), ?_, fun u => ?_, fun v => ?_⟩
  · exact ((hswap.comp' hG (fun _ => rfl)).comp' hswap' (fun _ => rfl)).comp' hF (fun _ => rfl)
  · show F ((G (((markStr u).map Sum.inl).map Sum.swap)).map Sum.swap) = _
    rw [show (((markStr u).map Sum.inl).map (Sum.swap : Option A₁ ⊕ Option A₂ → _))
      = (markStr u).map Sum.inr by simp [List.map_map, Function.comp_def]]
    rw [hGR u, show (((markStr u).map (Sum.inr : Option A₁ → Option B₂ ⊕ Option A₁)).map
      (Sum.swap : Option B₂ ⊕ Option A₁ → _)) = (markStr u).map Sum.inl by
      simp [List.map_map, Function.comp_def]]
    exact hFL u
  · show F ((G (((markStr v).map Sum.inr).map Sum.swap)).map Sum.swap) = _
    rw [show (((markStr v).map (Sum.inr : Option A₂ → Option A₁ ⊕ Option A₂)).map
      (Sum.swap : Option A₁ ⊕ Option A₂ → _)) = (markStr v).map Sum.inl by
      simp [List.map_map, Function.comp_def]]
    rw [hGL v, show (((markStr (f₂ v)).map (Sum.inl : Option B₂ → Option B₂ ⊕ Option A₁)).map
      (Sum.swap : Option B₂ ⊕ Option A₁ → _)) = (markStr (f₂ v)).map Sum.inr by
      simp [List.map_map, Function.comp_def]]
    exact hFR (f₂ v)

/-! ## Case distinction and concatenation -/

/-- The homomorphism that forgets the marker and the colour. -/
def unMark {B : Type} : Option B ⊕ Option B → List B
  | Sum.inl (some b) => [b]
  | Sum.inr (some b) => [b]
  | _ => []

lemma homOf_unMark_inl {B : Type} (l : List B) :
    homOf unMark ((markStr l).map Sum.inl) = l := by
  have key : ∀ l : List B, homOf unMark ((l.map (some : B → Option B)).map Sum.inl) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons b l ih => simpa [homOf, unMark] using ih
  simpa [homOf, unMark, markStr] using key l

lemma homOf_unMark_inr {B : Type} (l : List B) :
    homOf unMark ((markStr l).map Sum.inr) = l := by
  have key : ∀ l : List B, homOf unMark ((l.map (some : B → Option B)).map Sum.inr) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons b l ih => simpa [homOf, unMark] using ih
  simpa [homOf, unMark, markStr] using key l

open scoped Classical in
/-- **Case distinction over a regular language preserves polyregularity.** -/
theorem isPolyregular_cond {A B : Type} [Finite A] [Finite B] {f g : List A → List B}
    (hf : IsPolyregular f) (hg : IsPolyregular g) {L : Language A} (hL : L.IsRegular) :
    IsPolyregular (fun w => if w ∈ L then f w else g w) := by
  classical
  obtain ⟨F, hF, hFL, hFR⟩ := exists_polySum hf hg
  have hcol : IsPolyregular (fun w : List A => if w ∈ L then RegCl.colL w else RegCl.colR w) :=
    IsPolyregular.of_regular (IsRegularFun.of_rational
      (isRationalFun_ite_lang hL RegCl.isRationalFun_colL RegCl.isRationalFun_colR))
  have hhom : IsPolyregular (homOf (unMark : Option B ⊕ Option B → List B)) :=
    IsPolyregular.of_regular (IsRegularFun.of_rational (isRationalFun_homOf _))
  refine ((hcol.comp' hF (fun _ => rfl)).comp' hhom (fun _ => rfl)).congr (fun w => ?_)
  show homOf unMark (F (if w ∈ L then RegCl.colL w else RegCl.colR w)) = _
  by_cases hw : w ∈ L
  · rw [if_pos hw, if_pos hw]
    show homOf unMark (F ((markStr w).map Sum.inl)) = f w
    rw [hFL w, homOf_unMark_inl]
  · rw [if_neg hw, if_neg hw]
    show homOf unMark (F ((markStr w).map Sum.inr)) = g w
    rw [hFR w, homOf_unMark_inr]

/-- **Concatenation preserves polyregularity.** -/
theorem isPolyregular_concat {A B : Type} [Finite A] [Finite B] {f g : List A → List B}
    (hf : IsPolyregular f) (hg : IsPolyregular g) : IsPolyregular (fun w => f w ++ g w) := by
  obtain ⟨F, hF, hFL, hFR⟩ := exists_polySum hf hg
  haveI : Finite (Option A ⊕ Option A) := inferInstance
  haveI : Finite (Option B ⊕ Option B) := inferInstance
  -- the two coloured copies of the input, separated by the separator of the map lifting
  have hsplit : IsPolyregular (fun w : List A =>
      (RegCl.colL w).map some ++ ((none : Option (Option A ⊕ Option A)) ::
        (RegCl.colR w).map some)) := by
    refine IsPolyregular.of_regular (isRegularFun_concat
      ((IsRegularFun.of_rational RegCl.isRationalFun_colL).comp'
        (IsRegularFun.of_rational (isRationalFun_map some)) (fun _ => rfl))
      ((IsRegularFun.of_rational RegCl.isRationalFun_colR).comp'
        ((IsRegularFun.of_rational (isRationalFun_map some)).comp'
          (IsRegularFun.of_rational (isRationalFun_cons _)) (fun _ => rfl)) (fun _ => rfl)))
  have hml : IsPolyregular (mapLift F) := isPolyregular_mapLift hF
  have hhom : IsPolyregular
      (homOf (fun x : Option (Option B ⊕ Option B) =>
        match x with | none => [] | some y => unMark y)) :=
    IsPolyregular.of_regular (IsRegularFun.of_rational (isRationalFun_homOf _))
  refine ((hsplit.comp' hml (fun _ => rfl)).comp' hhom (fun _ => rfl)).congr (fun w => ?_)
  show homOf _ (mapLift F ((RegCl.colL w).map some ++ ((none : Option (Option A ⊕ Option A)) ::
    (RegCl.colR w).map some))) = f w ++ g w
  have hsplitSep : splitSep ((RegCl.colL w).map some ++ ((none : Option (Option A ⊕ Option A)) ::
      (RegCl.colR w).map some)) = [RegCl.colL w, RegCl.colR w] := by
    have h0 : splitSep ((none : Option (Option A ⊕ Option A)) :: (RegCl.colR w).map some)
        = [] :: splitSep ((RegCl.colR w).map some) := rfl
    have h1 : splitSep ((RegCl.colR w).map some) = [RegCl.colR w] := by
      have := splitSep_map_some_append (RegCl.colR w) ([] : List (Option (Option A ⊕ Option A)))
        [] [] rfl
      simpa using this
    rw [h1] at h0
    have := splitSep_map_some_append (RegCl.colL w)
      ((none : Option (Option A ⊕ Option A)) :: (RegCl.colR w).map some) [] [RegCl.colR w] h0
    simpa using this
  rw [mapLift, hsplitSep]
  show homOf _ (List.intercalate [none]
    [(F (RegCl.colL w)).map some, (F (RegCl.colR w)).map some]) = f w ++ g w
  have hL : F (RegCl.colL w) = (markStr (f w)).map Sum.inl := hFL w
  have hR : F (RegCl.colR w) = (markStr (g w)).map Sum.inr := hFR w
  rw [hL, hR]
  rw [show List.intercalate [(none : Option (Option B ⊕ Option B))]
      [(((markStr (f w)).map Sum.inl).map some), (((markStr (g w)).map Sum.inr).map some)]
    = (((markStr (f w)).map Sum.inl).map some) ++ ((none : Option (Option B ⊕ Option B)) ::
      (((markStr (g w)).map Sum.inr).map some)) by simp [List.intercalate]]
  rw [show homOf (fun x : Option (Option B ⊕ Option B) =>
      match x with | none => ([] : List B) | some y => unMark y)
      ((((markStr (f w)).map Sum.inl).map some) ++ ((none : Option (Option B ⊕ Option B)) ::
        (((markStr (g w)).map Sum.inr).map some)))
    = homOf (fun x : Option (Option B ⊕ Option B) =>
        match x with | none => ([] : List B) | some y => unMark y)
        (((markStr (f w)).map Sum.inl).map some)
      ++ homOf (fun x : Option (Option B ⊕ Option B) =>
        match x with | none => ([] : List B) | some y => unMark y)
        ((none : Option (Option B ⊕ Option B)) :: (((markStr (g w)).map Sum.inr).map some)) by
    simp [homOf]]
  have hcl : ∀ (l : List (Option B ⊕ Option B)),
      homOf (fun x : Option (Option B ⊕ Option B) =>
        match x with | none => ([] : List B) | some y => unMark y) (l.map some)
      = homOf unMark l := by
    intro l
    simp [homOf, List.map_map, Function.comp_def]
  rw [hcl]
  rw [show ((none : Option (Option B ⊕ Option B)) :: (((markStr (g w)).map Sum.inr).map some))
    = [none] ++ (((markStr (g w)).map Sum.inr).map some) from rfl]
  rw [show homOf (fun x : Option (Option B ⊕ Option B) =>
      match x with | none => ([] : List B) | some y => unMark y)
      ([none] ++ (((markStr (g w)).map Sum.inr).map some))
    = homOf (fun x : Option (Option B ⊕ Option B) =>
        match x with | none => ([] : List B) | some y => unMark y) [none]
      ++ homOf (fun x : Option (Option B ⊕ Option B) =>
        match x with | none => ([] : List B) | some y => unMark y)
        (((markStr (g w)).map Sum.inr).map some) by simp [homOf]]
  rw [hcl, homOf_unMark_inl, homOf_unMark_inr]
  simp [homOf]

end Transducers
