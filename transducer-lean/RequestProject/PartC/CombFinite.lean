/-
Claim `claim:finite-domain-regular-list-function` and Lemma
`lem:terms-define-string-homomorphisms` of Section *Combinators* of *Transducers* (M. Bojańczyk).

These two belong to the *converse* direction of Theorem `thm:regular-terms` -- that the regular
terms are expressively complete -- of which they are the first step: every type-to-type function
whose domain is a finite type is defined by a regular term, and hence so is every string-to-string
homomorphism, which is the map of such a function followed by concatenation.

The proof of the first is the book's, with one change of route.  The book reduces a finite domain
to a co-product `1 + ⋯ + 1` of copies of the unit type (Claim
`claim:finite-type-bijection-disjoint-units`) and then uses co-pairing.  Here the domain is taken
apart directly, by induction on a measure that decreases under the two rearrangements the proof
performs on a product,

    (X + Y) × A → (A × X) + (A × Y)   and   (X × Y) × A → X × (Y × A),

the first by swapping and distributivity, the second by re-associating.  The measure is
`Transducers.Ty.msr` below; the point of `A × B ↦ msr A · (1 + msr B)` is that the re-association
strictly decreases it.  The reduction to the unit type is then the base case `1 × A → A`, which is
a projection, and no bijection with `1 + ⋯ + 1` has to be built.  A type of the shape `A*` cannot
occur, because the elements of a type are never empty, so `A*` is infinite.
-/
import RequestProject.PartC.CombTerms

namespace Transducers

/-! ## The combinators, for the functions defined by a regular term -/

lemma IsRegularTermFun.pair {A B C : Ty} {f : A.Elt → B.Elt} {g : A.Elt → C.Elt}
    (hf : IsRegularTermFun f) (hg : IsRegularTermFun g) :
    IsRegularTermFun (A := A) (B := Ty.prod B C) (fun a => (f a, g a)) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨s.pair t, by funext a; rw [show (s.pair t).eval a = (s.eval a, t.eval a) from rfl, hs, ht]⟩

lemma IsRegularTermFun.copair {A B C : Ty} {f : A.Elt → C.Elt} {g : B.Elt → C.Elt}
    (hf : IsRegularTermFun f) (hg : IsRegularTermFun g) :
    IsRegularTermFun (A := Ty.sum A B) (B := C) (Sum.elim f g) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨s.copair t, ?_⟩
  funext x
  rw [show (s.copair t).eval x = Sum.elim s.eval t.eval x from rfl, hs, ht]

lemma IsRegularTermFun.mapList {A B : Ty} {f : A.Elt → B.Elt} (hf : IsRegularTermFun f) :
    IsRegularTermFun (A := Ty.list A) (B := Ty.list B) (fun l => l.map f) := by
  obtain ⟨t, ht⟩ := hf
  exact ⟨t.map, by funext l; rw [show (t.map).eval l = l.map t.eval from rfl, ht]⟩

/-! ## Constants -/

/-- **Every element of a type is a constant defined by a regular term.**  This is the case of a
function whose domain is the unit type. -/
theorem constTerm : ∀ (B : Ty) (b : B.Elt),
    IsRegularTermFun (A := Ty.one) (B := B) (fun _ => b) := by
  intro B
  induction B with
  | one =>
      intro b
      exact (IsRegularTermFun.of_term (RegTerm.id Ty.one)).congr (fun x => by cases b; rfl)
  | prod B1 B2 ih1 ih2 =>
      intro b
      exact ((ih1 b.1).pair (ih2 b.2)).congr (fun _ => rfl)
  | sum B1 B2 ih1 ih2 =>
      intro b
      cases b with
      | inl b1 =>
          exact ((ih1 b1).comp (IsRegularTermFun.of_term (RegTerm.inl B1 B2))).congr (fun _ => rfl)
      | inr b2 =>
          exact ((ih2 b2).comp (IsRegularTermFun.of_term (RegTerm.inr B1 B2))).congr (fun _ => rfl)
  | list B1 ih =>
      intro l
      induction l with
      | nil =>
          have h : IsRegularTermFun (A := Ty.one) (B := Ty.sum Ty.one (Ty.prod B1 (Ty.list B1)))
              (fun _ => Sum.inl ()) :=
            IsRegularTermFun.of_term (RegTerm.inl Ty.one (Ty.prod B1 (Ty.list B1)))
          exact (h.comp (IsRegularTermFun.of_term (RegTerm.cons B1))).congr (fun _ => rfl)
      | cons a l ihl =>
          have hpair : IsRegularTermFun (A := Ty.one) (B := Ty.prod B1 (Ty.list B1))
              (fun _ => (a, l)) := (ih a).pair ihl
          have hinr : IsRegularTermFun (A := Ty.one)
              (B := Ty.sum Ty.one (Ty.prod B1 (Ty.list B1))) (fun _ => Sum.inr (a, l)) :=
            (hpair.comp
              (IsRegularTermFun.of_term (RegTerm.inr Ty.one (Ty.prod B1 (Ty.list B1))))).congr
              (fun _ => rfl)
          exact (hinr.comp (IsRegularTermFun.of_term (RegTerm.cons B1))).congr (fun _ => rfl)

/-! ## The measure on the domain -/

/-- The measure on types that the induction of Claim `claim:finite-domain-regular-list-function`
decreases.  The clause for a product is what makes the re-association
`(X × Y) × A → X × (Y × A)` decrease it. -/
def Ty.msr : Ty → ℕ
  | .one => 1
  | .prod A B => A.msr * (1 + B.msr)
  | .sum A B => 1 + A.msr + B.msr
  | .list A => 1 + A.msr

lemma Ty.one_le_msr (A : Ty) : 1 ≤ A.msr := by
  induction A with
  | one => exact le_refl 1
  | prod A B ihA _ =>
      calc 1 = 1 * 1 := rfl
        _ ≤ A.msr * (1 + B.msr) := Nat.mul_le_mul ihA (by omega)
  | sum A B ihA _ => simp only [Ty.msr]; omega
  | list A ih => simp only [Ty.msr]; omega

/-! ## Functions with a finite domain -/

private lemma finite_left {α β : Type} [Nonempty β] (h : Finite (α × β)) : Finite α := by
  haveI := h
  exact Finite.of_injective (fun a : α => (a, Classical.arbitrary β))
    (fun a a' haa => (Prod.mk.injEq _ _ _ _ ▸ haa : a = a' ∧ _).1)

private lemma finite_right {α β : Type} [Nonempty α] (h : Finite (α × β)) : Finite β := by
  haveI := h
  exact Finite.of_injective (fun b : β => (Classical.arbitrary α, b))
    (fun b b' hbb => (Prod.mk.injEq _ _ _ _ ▸ hbb : _ ∧ b = b').2)

private lemma finite_inl {α β : Type} (h : Finite (α ⊕ β)) : Finite α := by
  haveI := h
  exact Finite.of_injective (Sum.inl : α → α ⊕ β) Sum.inl_injective

private lemma finite_inr {α β : Type} (h : Finite (α ⊕ β)) : Finite β := by
  haveI := h
  exact Finite.of_injective (Sum.inr : β → α ⊕ β) Sum.inr_injective

private lemma not_finite_list (α : Type) [Nonempty α] (h : Finite (List α)) : False := by
  haveI := h
  exact not_finite (List α)

private theorem finiteDomain_aux : ∀ (n : ℕ) (A : Ty), A.msr ≤ n → Finite A.Elt →
    ∀ (B : Ty) (f : A.Elt → B.Elt), IsRegularTermFun f := by
  intro n
  induction n with
  | zero =>
      intro A hA
      exact absurd hA (by have := A.one_le_msr; omega)
  | succ n ih =>
      intro A hA hfin B f
      match A with
      | .one => exact (constTerm B (f ())).congr (fun x => by cases x; rfl)
      | .list A1 =>
          exfalso
          haveI : Nonempty A1.Elt := ⟨default⟩
          exact not_finite_list A1.Elt hfin
      | .sum A1 A2 =>
          have hs : Finite (A1.Elt ⊕ A2.Elt) := hfin
          have hm : A1.msr ≤ n ∧ A2.msr ≤ n := by
            simp only [Ty.msr] at hA
            have h1 := A1.one_le_msr
            have h2 := A2.one_le_msr
            omega
          have h1 := ih A1 hm.1 (finite_inl hs) B (fun a => f (Sum.inl a))
          have h2 := ih A2 hm.2 (finite_inr hs) B (fun a => f (Sum.inr a))
          exact (h1.copair h2).congr (fun x => by cases x <;> rfl)
      | .prod A1 A2 =>
          match A1 with
          | .one =>
              have hp : Finite (Unit × A2.Elt) := hfin
              haveI : Nonempty Unit := ⟨()⟩
              have hm : A2.msr ≤ n := by
                simp only [Ty.msr] at hA
                omega
              have h := ih A2 hm (finite_right hp) B (fun a2 => f ((), a2))
              exact ((IsRegularTermFun.of_term (RegTerm.snd Ty.one A2)).comp h).congr
                (fun x => by obtain ⟨u, a2⟩ := x; cases u; rfl)
          | .list X =>
              exfalso
              haveI : Nonempty X.Elt := ⟨default⟩
              haveI : Nonempty A2.Elt := ⟨default⟩
              have hp : Finite ((List X.Elt) × A2.Elt) := hfin
              exact not_finite_list X.Elt (finite_left hp)
          | .prod X Y =>
              haveI : Nonempty X.Elt := ⟨default⟩
              haveI : Nonempty Y.Elt := ⟨default⟩
              haveI : Nonempty A2.Elt := ⟨default⟩
              have hp : Finite ((X.Elt × Y.Elt) × A2.Elt) := hfin
              haveI hxy : Finite (X.Elt × Y.Elt) := finite_left hp
              haveI hx : Finite X.Elt := finite_left hxy
              haveI hy : Finite Y.Elt := finite_right hxy
              haveI ha2 : Finite A2.Elt := finite_right hp
              have hm : (Ty.prod X (Ty.prod Y A2)).msr ≤ n := by
                simp only [Ty.msr] at hA ⊢
                have hx1 := X.one_le_msr
                have hy1 := Y.one_le_msr
                have ha1 := A2.one_le_msr
                nlinarith
              have hfinq : Finite (Ty.prod X (Ty.prod Y A2)).Elt := by
                show Finite (X.Elt × (Y.Elt × A2.Elt))
                infer_instance
              have h := ih (Ty.prod X (Ty.prod Y A2)) hm hfinq B
                (fun q => f ((q.1, q.2.1), q.2.2))
              have hrot : IsRegularTermFun (A := Ty.prod (Ty.prod X Y) A2)
                  (B := Ty.prod X (Ty.prod Y A2)) (fun p => (p.1.1, (p.1.2, p.2))) :=
                (((IsRegularTermFun.of_term (RegTerm.fst (Ty.prod X Y) A2)).comp
                    (IsRegularTermFun.of_term (RegTerm.fst X Y))).pair
                  (((IsRegularTermFun.of_term (RegTerm.fst (Ty.prod X Y) A2)).comp
                      (IsRegularTermFun.of_term (RegTerm.snd X Y))).pair
                    (IsRegularTermFun.of_term (RegTerm.snd (Ty.prod X Y) A2))))
              exact (hrot.comp h).congr (fun p => by
                obtain ⟨⟨x, y⟩, a2⟩ := p; rfl)
          | .sum X Y =>
              haveI : Nonempty X.Elt := ⟨default⟩
              haveI : Nonempty Y.Elt := ⟨default⟩
              haveI : Nonempty A2.Elt := ⟨default⟩
              have hp : Finite ((X.Elt ⊕ Y.Elt) × A2.Elt) := hfin
              haveI hxy : Finite (X.Elt ⊕ Y.Elt) := finite_left hp
              haveI hx : Finite X.Elt := finite_inl hxy
              haveI hy : Finite Y.Elt := finite_inr hxy
              haveI ha2 : Finite A2.Elt := finite_right hp
              have hmx : (Ty.prod A2 X).msr ≤ n := by
                simp only [Ty.msr] at hA ⊢
                have hx1 := X.one_le_msr
                have hy1 := Y.one_le_msr
                have ha1 := A2.one_le_msr
                nlinarith
              have hmy : (Ty.prod A2 Y).msr ≤ n := by
                simp only [Ty.msr] at hA ⊢
                have hx1 := X.one_le_msr
                have hy1 := Y.one_le_msr
                have ha1 := A2.one_le_msr
                nlinarith
              have hfx : Finite (Ty.prod A2 X).Elt := by
                show Finite (A2.Elt × X.Elt); infer_instance
              have hfy : Finite (Ty.prod A2 Y).Elt := by
                show Finite (A2.Elt × Y.Elt); infer_instance
              have h1 := ih (Ty.prod A2 X) hmx hfx B (fun r => f (Sum.inl r.2, r.1))
              have h2 := ih (Ty.prod A2 Y) hmy hfy B (fun r => f (Sum.inr r.2, r.1))
              have hswap : IsRegularTermFun (A := Ty.prod (Ty.sum X Y) A2)
                  (B := Ty.prod A2 (Ty.sum X Y)) (fun p => (p.2, p.1)) :=
                (IsRegularTermFun.of_term (RegTerm.snd (Ty.sum X Y) A2)).pair
                  (IsRegularTermFun.of_term (RegTerm.fst (Ty.sum X Y) A2))
              have hdistr := IsRegularTermFun.of_term (RegTerm.distr A2 X Y)
              have hcop := h1.copair h2
              exact ((hswap.comp hdistr).comp hcop).congr (fun p => by
                obtain ⟨x, a2⟩ := p
                cases x <;> rfl)

/-- **Claim `claim:finite-domain-regular-list-function`.**  Every type-to-type function whose
domain is a finite type is defined by a regular term. -/
theorem finite_domain_regular_list_function {A B : Ty} (hA : Finite A.Elt) (f : A.Elt → B.Elt) :
    IsRegularTermFun f :=
  finiteDomain_aux A.msr A (le_refl _) hA B f

/-- **Lemma `lem:terms-define-string-homomorphisms`.**  Every string-to-string homomorphism is
defined by a regular term: for a finite type `A`, the homomorphism `A* → B*` induced by a map
`A → B*` is the map of that function followed by concatenation. -/
theorem terms_define_string_homomorphisms {A B : Ty} (hA : Finite A.Elt)
    (f : A.Elt → (Ty.list B).Elt) :
    IsRegularTermFun (A := Ty.list A) (B := Ty.list B) (fun l => (l.map f).flatten) :=
  ((finite_domain_regular_list_function hA f).mapList).comp
    (IsRegularTermFun.of_term (RegTerm.concat B))

end Transducers
