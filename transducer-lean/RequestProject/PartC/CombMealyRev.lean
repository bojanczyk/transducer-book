/-
Lemma `lem:terms-define-reversible` of Section *Combinators* of *Transducers* (M. Bojańczyk):
every reversible Mealy machine is definable by a regular term.

The construction is the book's.  Each input letter is paired with the permutation of the state
space that it induces, group prefix multiplication turns the list of these pairs into the list of
their prefix products, the delay machine of Example `ex:delay` -- a flip-flop machine, hence
covered by Lemma `lem:terms-define-flip-flop` -- pairs every prefix product with the previous one,
and a letter-to-letter homomorphism reads the output letter off the two: the input letter is
recovered from the two prefix products by a group inverse, and so is the state before it.

The book puts an "arbitrary group structure, say a cyclic one" on the input alphabet in order to
recover the input letter.  Here the input alphabet `A` is embedded in the group of permutations of
`A + 1` instead, by `a ↦ swap 1 a`, which is injective because the image of `1` under it is `a`.
It plays exactly the role of the cyclic group, and it avoids having to choose a group structure on
a bare finite type.

The group whose prefix products are taken must be the set of elements of a *type*, since that is
what the atomic term of Definition `def:regular-terms` requires; its group structure is transported
along a bijection with the product of the two permutation groups by `Equiv.group`.
-/
import RequestProject.PartC.CombMealyFF

namespace Transducers

/-! ## Prefix products -/

lemma scanl_map_hom {M N : Type} [Monoid M] [Monoid N] (f : M → N)
    (hfm : ∀ x y, f (x * y) = f x * f y) :
    ∀ (l : List M) (x : M), (l.scanl (· * ·) x).map f = (l.map f).scanl (· * ·) (f x) := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons a l ih =>
      intro x
      rw [List.scanl_cons, List.map_cons, List.map_cons, List.scanl_cons, ih (x * a), hfm]

lemma prefixProd_map_hom {M N : Type} [Monoid M] [Monoid N] (f : M → N) (hf1 : f 1 = 1)
    (hfm : ∀ x y, f (x * y) = f x * f y) (l : List M) :
    (prefixProd l).map f = prefixProd (l.map f) := by
  unfold prefixProd
  rw [List.map_tail, scanl_map_hom f hfm l 1, hf1]

/-- Prefix products with an initial accumulator; `pprodFrom 1 = prefixProd`. -/
def pprodFrom {M : Type} [Monoid M] (x : M) (l : List M) : List M := (l.scanl (· * ·) x).tail

@[simp] lemma pprodFrom_nil {M : Type} [Monoid M] (x : M) : pprodFrom x ([] : List M) = [] := rfl

lemma pprodFrom_cons {M : Type} [Monoid M] (x a : M) (l : List M) :
    pprodFrom x (a :: l) = (x * a) :: pprodFrom (x * a) l := by
  unfold pprodFrom
  rw [List.scanl_cons, List.tail_cons]
  cases l with
  | nil => simp
  | cons b l => simp [List.scanl_cons]

lemma prefixProd_eq_pprodFrom {M : Type} [Monoid M] (l : List M) :
    prefixProd l = pprodFrom 1 l := rfl

/-- Prefix products commute with a bijection whose inverse is a monoid homomorphism. -/
lemma prefixProd_map_of_symm_hom {G H : Type} [Monoid G] [Monoid H] (e : G ≃ H)
    (h1 : e.symm 1 = 1) (hmul : ∀ x y : H, e.symm (x * y) = e.symm x * e.symm y) (m : List G) :
    prefixProd (m.map e) = (prefixProd m).map e := by
  have h := prefixProd_map_hom (⇑e.symm) h1 hmul (m.map e)
  rw [List.map_map] at h
  simp only [Function.comp_def, Equiv.symm_apply_apply, List.map_id'] at h
  calc prefixProd (m.map e) = ((prefixProd (m.map e)).map e.symm).map e := by
        rw [List.map_map]; simp
    _ = (prefixProd m).map e := by rw [h]

/-! ## The delay machine -/

/-- The delay machine of Example `ex:delay`: it pairs every letter with the previous one, using a
fixed value before the first letter. -/
def delayMealy {Z : Type} (z₀ : Z) : Mealy Z (Z × Z) Z where
  init := z₀
  step := fun q a => (a, (a, q))

lemma delayMealy_flipFlop {Z : Type} (z₀ : Z) : (delayMealy z₀).FlipFlop :=
  fun a => Or.inr ⟨a, fun _ => rfl⟩

/-- The list that the delay machine produces. -/
def delayList {Z : Type} : Z → List Z → List (Z × Z)
  | _, [] => []
  | p, x :: xs => (x, p) :: delayList x xs

lemma delayMealy_run {Z : Type} (z₀ : Z) :
    ∀ (p : Z) (l : List Z), (delayMealy z₀).run p l = delayList p l := by
  intro p l
  induction l generalizing p with
  | nil => rfl
  | cons x l ih => exact congrArg _ (ih x)

lemma delayList_map {Z W : Type} (f : Z → W) :
    ∀ (p : Z) (l : List Z),
      delayList (f p) (l.map f) = (delayList p l).map (fun q => (f q.1, f q.2)) := by
  intro p l
  induction l generalizing p with
  | nil => rfl
  | cons x l ih => exact congrArg _ (ih x)

/-! ## The construction -/

namespace RevMealy

variable {AE QE : Type} [DecidableEq AE]

/-- The embedding of the input alphabet into the permutations of `A + 1`. -/
def iota (a : AE) : Equiv.Perm (Option AE) := Equiv.swap none (some a)

/-- The left inverse of `iota`. -/
def unIota [Inhabited AE] (x : Equiv.Perm (Option AE)) : AE := (x none).getD default

@[simp] lemma unIota_iota [Inhabited AE] (a : AE) : unIota (iota a) = a := by
  simp [unIota, iota]

variable {BE : Type} (M : Mealy AE BE QE) (hM : M.Reversible)

/-- The permutation of the state space induced by a letter, inverted so that a product of them
acts as the composition in the reading order. -/
noncomputable def permOf (a : AE) : Equiv.Perm QE := (Equiv.ofBijective (M.letterTrans a) (hM a)).symm

omit [DecidableEq AE] in
lemma permOf_inv_apply (a : AE) (q : QE) : (permOf M hM a)⁻¹ q = M.letterTrans a q := rfl

/-- The group in which the prefix products are taken. -/
abbrev Grp (AE QE : Type) : Type := Equiv.Perm (Option AE) × Equiv.Perm QE

/-- Each letter, paired with its two group elements. -/
noncomputable def phi (a : AE) : Grp AE QE := (iota a, permOf M hM a)

/-- The state of the machine that a prefix product describes. -/
def accState (h : Grp AE QE) : QE := (h.2)⁻¹ M.init

/-- The output letter read off a prefix product and its predecessor. -/
def outH [Inhabited AE] (p : Grp AE QE × Grp AE QE) : BE :=
  (M.step (accState M p.2) (unIota ((p.2.1)⁻¹ * p.1.1))).2

lemma accState_mul [Inhabited AE] (acc : Grp AE QE) (a : AE) :
    accState M (acc * phi M hM a) = M.letterTrans a (accState M acc) := by
  show ((acc * phi M hM a).2)⁻¹ M.init = _
  have : (acc * phi M hM a).2 = acc.2 * permOf M hM a := rfl
  rw [this, mul_inv_rev]
  rw [Equiv.Perm.mul_apply]
  exact permOf_inv_apply M hM a _

lemma outH_mul [Inhabited AE] (acc : Grp AE QE) (a : AE) :
    outH M (acc * phi M hM a, acc) = (M.step (accState M acc) a).2 := by
  show (M.step (accState M acc) (unIota ((acc.1)⁻¹ * (acc * phi M hM a).1))).2 = _
  have : (acc * phi M hM a).1 = acc.1 * iota a := rfl
  rw [this, ← mul_assoc, inv_mul_cancel, one_mul, unIota_iota]

/-- **The run of a reversible machine, read off the delayed prefix products.** -/
lemma rev_run [Inhabited AE] :
    ∀ (acc : Grp AE QE) (w : List AE),
      (delayList acc (pprodFrom acc (w.map (phi M hM)))).map (outH M)
        = M.run (accState M acc) w := by
  intro acc w
  induction w generalizing acc with
  | nil => rfl
  | cons a w ih =>
      rw [List.map_cons, pprodFrom_cons]
      show outH M (acc * phi M hM a, acc)
        :: ((delayList (acc * phi M hM a) (pprodFrom (acc * phi M hM a)
              (w.map (phi M hM)))).map (outH M)) = _
      rw [ih (acc * phi M hM a), outH_mul M hM acc a, accState_mul M hM acc a]
      rfl

omit [DecidableEq AE] in
lemma accState_one [Inhabited AE] : accState M (1 : Grp AE QE) = M.init := by
  show (1 : Equiv.Perm QE)⁻¹ M.init = M.init
  simp

end RevMealy

/-! ## Lemma `lem:terms-define-reversible` -/

open RevMealy in
/-- The version of Lemma `lem:terms-define-reversible` for a machine whose alphabets and states
are the elements of types. -/
theorem tfun_reversible_eval {A B QT : Ty} (hA : Finite A.Elt) (hQ : Finite QT.Elt)
    (M : Mealy A.Elt B.Elt QT.Elt) (hM : M.Reversible) :
    IsRegularTermFun (A := .list A) (B := .list B) M.eval := by
  classical
  haveI := hA
  haveI := hQ
  haveI : Finite (Grp A.Elt QT.Elt) := inferInstance
  haveI : Nonempty (Grp A.Elt QT.Elt) := ⟨1⟩
  obtain ⟨PT, ⟨eH⟩, hPf⟩ := exists_ty_equiv (Grp A.Elt QT.Elt)
  letI grp : Group PT.Elt := Equiv.group eH.symm
  have hhom : ∀ x y : PT.Elt, eH.symm (x * y) = eH.symm x * eH.symm y := by
    intro x y
    exact eH.symm_apply_apply _
  have hone : eH.symm (1 : PT.Elt) = 1 := eH.symm_apply_apply _
  -- the four steps
  have hphi : IsRegularTermFun (A := .list A) (B := .list PT)
      (fun l => l.map (fun a => eH (phi M hM a))) := tfun_mapRen hA _
  have hpref : IsRegularTermFun (A := .list PT) (B := .list PT) (fun l => prefixProd l) :=
    ⟨RegTerm.pref PT grp hPf, rfl⟩
  have hdelay : IsRegularTermFun (A := .list PT) (B := .list (.prod PT PT))
      (delayMealy (eH 1)).eval :=
    tfun_flipFlop_eval hPf hPf _ (delayMealy_flipFlop _)
  haveI : Finite (Ty.prod PT PT).Elt := by
    show Finite (PT.Elt × PT.Elt); haveI := hPf; infer_instance
  have hout : IsRegularTermFun (A := .list (.prod PT PT)) (B := .list B)
      (fun l => l.map (fun p => outH M (eH.symm p.1, eH.symm p.2))) :=
    tfun_mapRen inferInstance _
  refine (hphi.comp (hpref.comp (hdelay.comp hout))).congr ?_
  intro l
  have h1 : l.map (fun a => eH (phi M hM a)) = (l.map (phi M hM)).map eH := by
    simp [List.map_map, Function.comp_def]
  have h2 : prefixProd ((l.map (phi M hM)).map eH)
      = (prefixProd (l.map (phi M hM))).map eH :=
    prefixProd_map_of_symm_hom eH hone hhom _
  have h3 : (delayMealy (eH 1)).eval ((prefixProd (l.map (phi M hM))).map eH)
      = (delayList (1 : Grp A.Elt QT.Elt) (prefixProd (l.map (phi M hM)))).map
        (fun q => (eH q.1, eH q.2)) := by
    show (delayMealy (eH 1)).run (eH 1) _ = _
    rw [delayMealy_run]
    exact delayList_map eH 1 _
  have h4 := rev_run M hM (1 : Grp A.Elt QT.Elt) l
  rw [accState_one M] at h4
  show ((delayMealy (eH 1)).eval (prefixProd (l.map (fun a => eH (phi M hM a))))).map
      (fun p => outH M (eH.symm p.1, eH.symm p.2)) = M.eval l
  rw [h1, h2, h3, List.map_map]
  simp only [Function.comp_def, Equiv.symm_apply_apply]
  exact h4

/-- **Lemma `lem:terms-define-reversible`.**  Every reversible Mealy machine is definable by a
regular term. -/
theorem terms_define_reversible {X Y : Type} (hX : Finite X) (hY : Finite Y)
    {g : List X → List Y} (h : IsReversibleMealy g) : TermStrFun g := by
  obtain ⟨Q, hQ, M, hMg, hRev⟩ := h
  subst hMg
  haveI := hX
  haveI := hY
  haveI := hQ
  by_cases hne : Nonempty X
  case neg => exact termStrFun_of_isEmpty_dom _ (not_nonempty_iff.1 hne)
  by_cases hne' : Nonempty Y
  case neg => exact termStrFun_of_isEmpty_cod _ (not_nonempty_iff.1 hne')
  haveI := hne
  haveI := hne'
  haveI : Nonempty Q := ⟨M.init⟩
  obtain ⟨A, ⟨eA⟩, hAf⟩ := exists_ty_equiv X
  obtain ⟨B, ⟨eB⟩, hBf⟩ := exists_ty_equiv Y
  obtain ⟨QT, ⟨eQ⟩, hQf⟩ := exists_ty_equiv Q
  refine termStrFun_of_one A B hBf eA.symm eB ?_
  exact (tfun_reversible_eval hAf hQf (M.transport eA.symm eB eQ)
    (Mealy.reversible_transport hRev _ _ _)).congr
    (fun l => Mealy.eval_transport M eA.symm eB eQ l)

end Transducers
