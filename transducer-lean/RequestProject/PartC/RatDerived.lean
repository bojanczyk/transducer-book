/-
Derived rational terms: the toolbox of the converse direction of Theorem `thm:rational-terms` of
Section *Combinators* of *Transducers* (M. Bojańczyk).

This is the counterpart of `CombDerived.lean` for the rational terms, and the places where the two
differ are exactly the places where the regular development uses pairing, which the rational terms
do not have:

* the singleton list `a ↦ [a]` adjoins a unit on the right and replaces it by the empty list,
  which is what the proof of Theorem `thm:rational-terms` prescribes for `pureterm`;
* prepending or appending a fixed block adjoins a unit on the corresponding side;
* the finite case distinction comes in two versions, one for each coordinate of a product, proved
  from the two distributivities -- the second one is what the right-to-left flip-flop machines
  need, and it is the reason the book adds left distributivity.

Swapping the coordinates of a product is *not* here, and cannot be: it is not rational under
string representation.
-/
import RequestProject.PartC.RatFinite

namespace Transducers

/-! ## Lists: the empty list, singletons and concatenation -/

lemma rtfun_nil (A : Ty) : IsRatTermFun (A := .one) (B := .list A) (fun _ => []) :=
  ratConstTerm (.list A) []

/-- The singleton list.  This is the implementation of `pureterm` that the proof of Theorem
`thm:rational-terms` gives: adjoin a unit and replace it by the empty list. -/
lemma rtfun_pure (A : Ty) : IsRatTermFun (A := A) (B := .list A) (fun a => [a]) := by
  refine ((rtfun_appendOne A).comp
    ((((rtfun_id A).prodMap (rtfun_const .one (.list A) [])).comp
      (rtfun_inr .one (.prod A (.list A)))).comp (rtfun_cons A))).congr ?_
  intro a; rfl

/-- The concatenation of two lists, which the book calls `binconc`. -/
lemma rtfun_append (A : Ty) :
    IsRatTermFun (A := .prod (.list A) (.list A)) (B := .list A)
      (fun p : List A.Elt × List A.Elt => p.1 ++ p.2) := by
  refine ((((rtfun_id (.list A)).prodMap (rtfun_pure (.list A))).comp
      (rtfun_inr .one (.prod (.list A) (.list (.list A))))).comp
      ((rtfun_cons (.list A)).comp (rtfun_concat A))).congr ?_
  have h : ∀ x y : List A.Elt, ([x, y] : List (List A.Elt)).flatten = x ++ y := by
    intro x y; simp
  rintro ⟨u, v⟩
  exact h u v

/-- Appending a fixed block to the output of a term. -/
lemma rtfun_appendConst {A T : Ty} {u : A.Elt → List T.Elt}
    (hu : IsRatTermFun (A := A) (B := .list T) u) (v : List T.Elt) :
    IsRatTermFun (A := A) (B := .list T) (fun a => u a ++ v) := by
  refine (hu.comp ((rtfun_appendOne (.list T)).comp
    (((rtfun_id (.list T)).prodMap (rtfun_const .one (.list T) v)).comp
      (rtfun_append T)))).congr ?_
  intro a; rfl

/-- Prepending a fixed block to the output of a term. -/
lemma rtfun_prependConst {A T : Ty} {u : A.Elt → List T.Elt}
    (hu : IsRatTermFun (A := A) (B := .list T) u) (v : List T.Elt) :
    IsRatTermFun (A := A) (B := .list T) (fun a => v ++ u a) := by
  refine (hu.comp ((rtfun_prependOne (.list T)).comp
    (((rtfun_const .one (.list T) v).prodMap (rtfun_id (.list T))).comp
      (rtfun_append T)))).congr ?_
  intro a; rfl

/-- Prepending a fixed element to a list. -/
lemma rtfun_consFixed (A : Ty) (a : A.Elt) :
    IsRatTermFun (A := .list A) (B := .list A) (fun l => a :: l) :=
  (rtfun_prependConst (rtfun_id (.list A)) [a]).congr (fun _ => rfl)

/-- Appending a fixed element to a list. -/
lemma rtfun_snocFixed (A : Ty) (a : A.Elt) :
    IsRatTermFun (A := .list A) (B := .list A) (fun l : List A.Elt => l ++ [a]) :=
  rtfun_appendConst (rtfun_id (.list A)) [a]

/-- **Claim `claim:head` for rational terms.**  The first element of a nonempty list. -/
theorem rat_claim_head (A : Ty) :
    IsRatTermFun (A := .list A) (B := A) (fun l => l.headI) := by
  refine ((rtfun_uncons A).comp
    ((ratConstTerm A default).copair (rtfun_fst A (.list A)))).congr ?_
  intro l
  cases l with
  | nil => rfl
  | cons a l => rfl

lemma rtfun_tail (A : Ty) :
    IsRatTermFun (A := .list A) (B := .list A) (fun l => l.tail) := by
  refine ((rtfun_uncons A).comp
    ((rtfun_const .one (.list A) []).copair (rtfun_snd A (.list A)))).congr ?_
  intro l
  cases l with
  | nil => rfl
  | cons a l => rfl

/-- A letter-to-letter renaming of a list. -/
lemma rtfun_mapRen {A B : Ty} (hA : Finite A.Elt) (h : A.Elt → B.Elt) :
    IsRatTermFun (A := .list A) (B := .list B) (fun l => l.map h) :=
  (rat_finite_domain hA h).mapList

/-! ## Finite case distinction -/

private lemma rtfun_unitsCases : ∀ (n : ℕ) {T U : Ty} {g : (Ty.units n).Elt → T.Elt → U.Elt},
    (∀ x, IsRatTermFun (g x)) →
      IsRatTermFun (A := .prod (Ty.units n) T) (B := U) (fun p => g p.1 p.2) := by
  intro n
  induction n with
  | zero =>
      intro T U g hg
      exact ((rtfun_snd .one T).comp (hg ())).congr (fun p => by
        obtain ⟨u, t⟩ := p; cases u; rfl)
  | succ n ih =>
      intro T U g hg
      have h1 : IsRatTermFun (A := .prod .one T) (B := U)
          (fun q => g (Sum.inl ()) q.2) := (rtfun_snd .one T).comp (hg (Sum.inl ()))
      have h2 : IsRatTermFun (A := .prod (Ty.units n) T) (B := U)
          (fun q => g (Sum.inr q.1) q.2) := ih (g := fun x t => g (Sum.inr x) t)
            (fun x => hg (Sum.inr x))
      refine ((rtfun_distl .one (Ty.units n) T).comp (h1.copair h2)).congr ?_
      rintro ⟨x, t⟩
      cases x with
      | inl u => cases u; rfl
      | inr x => rfl

private lemma rtfun_unitsCasesR : ∀ (n : ℕ) {T U : Ty} {g : (Ty.units n).Elt → T.Elt → U.Elt},
    (∀ x, IsRatTermFun (g x)) →
      IsRatTermFun (A := .prod T (Ty.units n)) (B := U) (fun p => g p.2 p.1) := by
  intro n
  induction n with
  | zero =>
      intro T U g hg
      exact ((rtfun_fst T .one).comp (hg ())).congr (fun p => by
        obtain ⟨t, u⟩ := p; cases u; rfl)
  | succ n ih =>
      intro T U g hg
      have h1 : IsRatTermFun (A := .prod T .one) (B := U)
          (fun q => g (Sum.inl ()) q.1) := (rtfun_fst T .one).comp (hg (Sum.inl ()))
      have h2 : IsRatTermFun (A := .prod T (Ty.units n)) (B := U)
          (fun q => g (Sum.inr q.2) q.1) := ih (g := fun x t => g (Sum.inr x) t)
            (fun x => hg (Sum.inr x))
      refine ((rtfun_distr T .one (Ty.units n)).comp (h1.copair h2)).congr ?_
      rintro ⟨t, x⟩
      cases x with
      | inl u => cases u; rfl
      | inr x => rfl

/-- **Finite case distinction on the first coordinate.**  A rational term may branch on the value
of a coordinate of a finite type, carrying an arbitrary value along. -/
theorem rtfun_finCases {F T U : Ty} (hF : Finite F.Elt) {g : F.Elt → T.Elt → U.Elt}
    (hg : ∀ x, IsRatTermFun (g x)) :
    IsRatTermFun (A := .prod F T) (B := U) (fun p => g p.1 p.2) := by
  classical
  obtain ⟨n, enc, henc, hinj⟩ := rtfun_finEnc F hF
  haveI : Nonempty F.Elt := ⟨default⟩
  have h := rtfun_unitsCases n (T := T) (U := U)
    (g := fun x t => g (Function.invFun enc x) t) (fun x => hg _)
  refine ((henc.prodMap (rtfun_id T)).comp h).congr ?_
  rintro ⟨x, t⟩
  dsimp only
  rw [Function.leftInverse_invFun hinj x]

/-- **Finite case distinction on the second coordinate.**  This is the version that left
distributivity is added for: the right-to-left machines produce the finite value on the right. -/
theorem rtfun_finCasesR {T F U : Ty} (hF : Finite F.Elt) {g : F.Elt → T.Elt → U.Elt}
    (hg : ∀ x, IsRatTermFun (g x)) :
    IsRatTermFun (A := .prod T F) (B := U) (fun p => g p.2 p.1) := by
  classical
  obtain ⟨n, enc, henc, hinj⟩ := rtfun_finEnc F hF
  haveI : Nonempty F.Elt := ⟨default⟩
  have h := rtfun_unitsCasesR n (T := T) (U := U)
    (g := fun x t => g (Function.invFun enc x) t) (fun x => hg _)
  refine (((rtfun_id T).prodMap henc).comp h).congr ?_
  rintro ⟨t, x⟩
  dsimp only
  rw [Function.leftInverse_invFun hinj x]

end Transducers
