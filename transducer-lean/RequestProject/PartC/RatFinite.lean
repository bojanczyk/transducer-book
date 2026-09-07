/-
Functions with a finite domain are definable by rational terms.  This is the first step of the
converse direction of Theorem `thm:rational-terms` of Section *Combinators* of *Transducers*
(M. Bojańczyk), and the counterpart, for the rational terms, of Claim
`claim:finite-domain-regular-list-function` and Lemma `lem:terms-define-string-homomorphisms` of
`CombFinite.lean`.

The route is the book's, which is the one the proof of Theorem `thm:rational-terms` prescribes for
the rational case: a finite type is put in bijection with a co-product `1 + ⋯ + 1` of copies of the
unit type, using *both* kinds of distributivity, and a function out of such a co-product is a
co-pairing of constants.  Two points where the regular development uses pairing are handled as the
book says:

* the direction `1 → 1 × ⋯ × 1` adjoins units, `Transducers.rtfun_prependOne`, where the regular
  proof uses the diagonal;
* the rearrangement `(X + Y) × A → (X × A) + (Y × A)` is left distributivity, an atomic function of
  the rational terms, where the regular proof composes swapping with the other distributivity.

Only the direction `A → 1 + ⋯ + 1` has to be a term: the other direction is used solely to *define*
the function on `1 + ⋯ + 1` whose composite with it is the given function, and any function out of
a finite co-product of units is a term.  So the statement proved here,
`Transducers.rtfun_finEnc`, asks for an injective term-definable encoding rather than for a
bijection definable in both directions.
-/
import RequestProject.PartC.RatTerms
import RequestProject.PartC.CombDerived

namespace Transducers

/-! ## Constants -/

/-- **Every element of a type is a constant defined by a rational term.** -/
theorem ratConstTerm : ∀ (B : Ty) (b : B.Elt), IsRatTermFun (A := Ty.one) (B := B) (fun _ => b) := by
  intro B
  induction B with
  | one => intro b; exact (rtfun_id Ty.one).congr (fun x => by cases b; rfl)
  | prod B1 B2 ih1 ih2 =>
      intro b
      exact ((rtfun_appendOne Ty.one).comp ((ih1 b.1).prodMap (ih2 b.2))).congr (fun _ => rfl)
  | sum B1 B2 ih1 ih2 =>
      intro b
      cases b with
      | inl b1 => exact ((ih1 b1).comp (rtfun_inl B1 B2)).congr (fun _ => rfl)
      | inr b2 => exact ((ih2 b2).comp (rtfun_inr B1 B2)).congr (fun _ => rfl)
  | list B1 ih =>
      intro l
      induction l with
      | nil =>
          exact ((rtfun_inl Ty.one (Ty.prod B1 (Ty.list B1))).comp (rtfun_cons B1)).congr
            (fun _ => rfl)
      | cons a l ihl =>
          have hpair : IsRatTermFun (A := Ty.one) (B := Ty.prod B1 (Ty.list B1))
              (fun _ => (a, l)) :=
            ((rtfun_appendOne Ty.one).comp ((ih a).prodMap ihl)).congr (fun _ => rfl)
          exact ((hpair.comp (rtfun_inr Ty.one (Ty.prod B1 (Ty.list B1)))).comp
            (rtfun_cons B1)).congr (fun _ => rfl)

/-! ## The unique function into the unit type -/

/-- **Claim `claim:bang-definable` for rational terms.**  For every type `A`, the unique function
`A → 1` is definable by a rational term. -/
theorem rat_bang_definable : ∀ A : Ty, IsRatTermFun (A := A) (B := .one) (fun _ => ()) := by
  intro A
  induction A with
  | one => exact (rtfun_id .one).congr (fun a => by cases a; rfl)
  | prod A B ihA _ => exact ((rtfun_fst A B).comp ihA).congr (fun _ => rfl)
  | sum A B ihA ihB => exact (ihA.copair ihB).congr (fun x => by cases x <;> rfl)
  | list A ihA =>
      refine ((rtfun_uncons A).comp
        (((rtfun_id .one)).copair ((rtfun_fst A (.list A)).comp ihA))).congr ?_
      intro l
      cases l with
      | nil => rfl
      | cons a l => rfl

/-- Every constant function is definable by a rational term. -/
lemma rtfun_const (A B : Ty) (b : B.Elt) : IsRatTermFun (A := A) (B := B) (fun _ => b) :=
  ((rat_bang_definable A).comp (ratConstTerm B b)).congr (fun _ => rfl)

/-! ## Two rearrangements -/

/-- Associativity of the co-product, which co-pairing gives. -/
lemma rtfun_sumAssoc (A B C : Ty) :
    IsRatTermFun (A := .sum (.sum A B) C) (B := .sum A (.sum B C))
      (fun x => match x with
        | Sum.inl (Sum.inl a) => Sum.inl a
        | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
        | Sum.inr c => Sum.inr (Sum.inr c)) := by
  refine (((rtfun_inl A (.sum B C)).copair
    ((rtfun_inl B C).comp (rtfun_inr A (.sum B C)))).copair
    ((rtfun_inr B C).comp (rtfun_inr A (.sum B C)))).congr ?_
  rintro (( a | b) | c) <;> rfl

/-- The inverse of left distributivity, which co-pairing and the functoriality combinator for
products give. -/
lemma rtfun_undistl (A B C : Ty) :
    IsRatTermFun (A := .sum (.prod A C) (.prod B C)) (B := .prod (.sum A B) C)
      (fun x => match x with
        | Sum.inl p => (Sum.inl p.1, p.2)
        | Sum.inr q => (Sum.inr q.1, q.2)) := by
  refine (((rtfun_inl A B).prodMap (rtfun_id C)).copair
    (((rtfun_inr A B).prodMap (rtfun_id C)))).congr ?_
  rintro (p | q) <;> rfl

/-! ## Encoding a finite type into `1 + ⋯ + 1` -/

/-- A co-product of two types of the form `1 + ⋯ + 1` is encoded into one of them, by a rational
term. -/
lemma unitsSumEnc : ∀ (n m : ℕ), ∃ (k : ℕ) (enc : ((Ty.units n).Elt ⊕ (Ty.units m).Elt) →
      (Ty.units k).Elt),
      IsRatTermFun (A := .sum (Ty.units n) (Ty.units m)) (B := Ty.units k) enc ∧
        Function.Injective enc := by
  intro n
  induction n with
  | zero =>
      intro m
      exact ⟨m + 1, fun x => x, rtfun_id _, fun _ _ h => h⟩
  | succ n ih =>
      intro m
      obtain ⟨k, enc, henc, hinj⟩ := ih m
      refine ⟨k + 1, fun x => match x with
        | Sum.inl (Sum.inl u) => Sum.inl u
        | Sum.inl (Sum.inr y) => Sum.inr (enc (Sum.inl y))
        | Sum.inr z => Sum.inr (enc (Sum.inr z)), ?_, ?_⟩
      · refine ((rtfun_sumAssoc Ty.one (Ty.units n) (Ty.units m)).comp
          ((rtfun_id Ty.one).sumMap henc)).congr ?_
        rintro ((u | y) | z) <;> rfl
      · rintro ((u | y) | z) ((u' | y') | z') h
        · cases u; cases u'; rfl
        · exact absurd h (by simp)
        · exact absurd h (by simp)
        · exact absurd h (by simp)
        · have h2 : Sum.inl y = (Sum.inl y' : (Ty.units n).Elt ⊕ (Ty.units m).Elt) :=
            hinj (Sum.inr.inj h)
          rw [Sum.inl.inj h2]
        · exact absurd (hinj (Sum.inr.inj h)) (by simp)
        · exact absurd h (by simp)
        · exact absurd (hinj (Sum.inr.inj h)) (by simp)
        · have h2 : Sum.inr z = (Sum.inr z' : (Ty.units n).Elt ⊕ (Ty.units m).Elt) :=
            hinj (Sum.inr.inj h)
          rw [Sum.inr.inj h2]

/-- A product of two types of the form `1 + ⋯ + 1` is encoded into one of them, by a rational
term. -/
lemma unitsProdEnc : ∀ (n m : ℕ), ∃ (k : ℕ) (enc : ((Ty.units n).Elt × (Ty.units m).Elt) →
      (Ty.units k).Elt),
      IsRatTermFun (A := .prod (Ty.units n) (Ty.units m)) (B := Ty.units k) enc ∧
        Function.Injective enc := by
  intro n
  induction n with
  | zero =>
      intro m
      refine ⟨m, fun p => p.2, rtfun_snd _ _, ?_⟩
      rintro ⟨u, x⟩ ⟨u', x'⟩ h
      cases u; cases u'
      exact congrArg (fun z => ((), z)) h
  | succ n ih =>
      intro m
      obtain ⟨k, enc, henc, hinj⟩ := ih m
      obtain ⟨k', enc', henc', hinj'⟩ := unitsSumEnc m k
      refine ⟨k', fun p => match p with
        | (Sum.inl _, x) => enc' (Sum.inl x)
        | (Sum.inr y, x) => enc' (Sum.inr (enc (y, x))), ?_, ?_⟩
      · refine ((rtfun_distl Ty.one (Ty.units n) (Ty.units m)).comp
          (((rtfun_snd Ty.one (Ty.units m)).sumMap henc).comp henc')).congr ?_
        rintro ⟨(u | y), x⟩ <;> rfl
      · rintro ⟨(u | y), x⟩ ⟨(u' | y'), x'⟩ h
        · cases u; cases u'
          have h2 : (Sum.inl x : (Ty.units m).Elt ⊕ (Ty.units k).Elt) = Sum.inl x' := hinj' h
          rw [Sum.inl.inj h2]
        · exact absurd (hinj' h) (by simp)
        · exact absurd (hinj' h) (by simp)
        · have h2 : (Sum.inr (enc (y, x)) : (Ty.units m).Elt ⊕ (Ty.units k).Elt)
              = Sum.inr (enc (y', x')) := hinj' h
          have h3 := hinj (Sum.inr.inj h2)
          rw [Prod.mk.injEq] at h3
          rw [h3.1, h3.2]

/-- **Every finite type is encoded into a type of the form `1 + ⋯ + 1` by a rational term.** -/
theorem rtfun_finEnc : ∀ (A : Ty), Finite A.Elt →
    ∃ (n : ℕ) (enc : A.Elt → (Ty.units n).Elt),
      IsRatTermFun (A := A) (B := Ty.units n) enc ∧ Function.Injective enc := by
  intro A
  induction A with
  | one => intro _; exact ⟨0, fun x => x, rtfun_id _, fun _ _ h => h⟩
  | prod A B ihA ihB =>
      intro hfin
      haveI : Nonempty A.Elt := ⟨default⟩
      haveI : Nonempty B.Elt := ⟨default⟩
      haveI hp : Finite (A.Elt × B.Elt) := hfin
      have hA : Finite A.Elt :=
        Finite.of_injective (fun a : A.Elt => (a, (default : B.Elt))) (fun a a' h =>
          (Prod.mk.injEq _ _ _ _ ▸ h : a = a' ∧ _).1)
      have hB : Finite B.Elt :=
        Finite.of_injective (fun b : B.Elt => ((default : A.Elt), b)) (fun b b' h =>
          (Prod.mk.injEq _ _ _ _ ▸ h : _ ∧ b = b').2)
      obtain ⟨n, encA, hencA, hinjA⟩ := ihA hA
      obtain ⟨m, encB, hencB, hinjB⟩ := ihB hB
      obtain ⟨k, enc, henc, hinj⟩ := unitsProdEnc n m
      refine ⟨k, fun p => enc (encA p.1, encB p.2), (hencA.prodMap hencB).comp henc, ?_⟩
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h2 := hinj h
      rw [Prod.mk.injEq] at h2
      exact Prod.ext (hinjA h2.1) (hinjB h2.2)
  | sum A B ihA ihB =>
      intro hfin
      haveI hs : Finite (A.Elt ⊕ B.Elt) := hfin
      have hA : Finite A.Elt := Finite.of_injective (Sum.inl : A.Elt → A.Elt ⊕ B.Elt)
        Sum.inl_injective
      have hB : Finite B.Elt := Finite.of_injective (Sum.inr : B.Elt → A.Elt ⊕ B.Elt)
        Sum.inr_injective
      obtain ⟨n, encA, hencA, hinjA⟩ := ihA hA
      obtain ⟨m, encB, hencB, hinjB⟩ := ihB hB
      obtain ⟨k, enc, henc, hinj⟩ := unitsSumEnc n m
      refine ⟨k, fun x => enc (Sum.map encA encB x), (hencA.sumMap hencB).comp henc, ?_⟩
      rintro (a | b) (a' | b') h <;> have h2 := hinj h <;> simp only [Sum.map] at h2
      · exact congrArg Sum.inl (hinjA (Sum.inl.inj h2))
      · exact absurd h2 (by simp)
      · exact absurd h2 (by simp)
      · exact congrArg Sum.inr (hinjB (Sum.inr.inj h2))
  | list A _ =>
      intro hfin
      haveI : Nonempty A.Elt := ⟨default⟩
      haveI : Finite (List A.Elt) := hfin
      exact absurd hfin (by
        intro h
        haveI := h
        exact not_finite (List A.Elt))

/-! ## Functions out of a finite type -/

/-- Every function out of a type of the form `1 + ⋯ + 1` is definable by a rational term. -/
lemma rtfun_unitsOut : ∀ (n : ℕ) (B : Ty) (g : (Ty.units n).Elt → B.Elt),
    IsRatTermFun (A := Ty.units n) (B := B) g := by
  intro n
  induction n with
  | zero => intro B g; exact (ratConstTerm B (g ())).congr (fun x => by cases x; rfl)
  | succ n ih =>
      intro B g
      refine ((ratConstTerm B (g (Sum.inl ()))).copair
        (ih B (fun x => g (Sum.inr x)))).congr ?_
      rintro (u | x)
      · cases u; rfl
      · rfl

/-- **Claim `claim:finite-domain-regular-list-function` for rational terms.**  Every type-to-type
function whose domain is a finite type is defined by a rational term. -/
theorem rat_finite_domain {A B : Ty} (hA : Finite A.Elt) (f : A.Elt → B.Elt) : IsRatTermFun f := by
  classical
  obtain ⟨n, enc, henc, hinj⟩ := rtfun_finEnc A hA
  haveI : Nonempty A.Elt := ⟨default⟩
  refine (henc.comp (rtfun_unitsOut n B (fun x => f (Function.invFun enc x)))).congr ?_
  intro a
  dsimp only
  rw [Function.leftInverse_invFun hinj a]

/-- **Lemma `lem:terms-define-string-homomorphisms` for rational terms.**  Every string-to-string
homomorphism is defined by a rational term. -/
theorem rat_terms_define_string_homomorphisms {A B : Ty} (hA : Finite A.Elt)
    (f : A.Elt → (Ty.list B).Elt) :
    IsRatTermFun (A := Ty.list A) (B := Ty.list B) (fun l => (l.map f).flatten) :=
  ((rat_finite_domain hA f).mapList).comp (rtfun_concat B)

end Transducers
