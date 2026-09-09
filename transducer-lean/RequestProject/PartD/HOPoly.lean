/-
Part D, Section *A functional programming language*: the closure properties of the polyregular
functions between types that the proof of Theorem `thm:higher-order-terms` is built from.

Three of them are new, and they are the only place in the proof of Theorem
`thm:higher-order-terms` where a polyregular function is constructed by hand.

* `Transducers.isRegularUnderRepr_const` -- a constant function is regular under string
  representation.  The term calculus of Definition `def:polyregular-terms` has no term for a
  constant function of an arbitrary type, but a constant string function is rational, so the
  constant functions are available here.

* `Transducers.IsPolyregularUnderRepr.cond` -- a case distinction driven by a polyregular
  `P → 1 + 1`.  The point is that the test is *not* assumed to be a regular language of
  representations: the tag is computed by a polyregular function, and the first letter of its
  output, which is `L` or `R`, is read by a regular test *after* the tag has been computed.

* `Transducers.isPolyregularUnderRepr_dup` -- the distribution of a parameter over a list,

      P × Q*  →  (P × Q)*        (p, [q₁,…,qₙ]) ↦ [(p,q₁),…,(p,qₙ)],

  and its consequence `Transducers.IsPolyregularUnderRepr.mapParam`, the *map with a parameter*:
  if `ℓ : P → Q*` and `f : P × Q → R` are polyregular then so is `p ↦ (ℓ p).map (f (p, ·))`.
  This is the one closure property that is not available for the regular functions -- it copies
  the parameter once per list entry, so its output is quadratic -- and it is exactly the extra
  strength that the higher-order features of Definition `def:higher-order-terms` need: the body of
  a `map` may mention the variables of the surrounding term.  It is obtained from the new atomic
  function `split` of Definition `def:polyregular-terms`: the parameter is put in front of the
  list, as the entry `L p` of a list over `P + Q`, and every way of cutting that list into a
  prefix and a suffix whose first entries are `L p` and `R q` contributes the pair `(p,q)`.
-/
import RequestProject.PartD.PolySplitsAtom

namespace Transducers

open Comb

/-! ## Constants -/

/-- **A constant function is regular under string representation.** -/
theorem isRegularUnderRepr_const {A B : Ty} (b : B.Elt) :
    IsRegularUnderRepr (fun _ : A.Elt => b) :=
  ⟨fun _ => B.repr b, IsRegularFun.of_rational (isRationalFun_const _), fun _ => rfl⟩

/-- A constant function is polyregular under string representation. -/
theorem isPolyregularUnderRepr_const {A B : Ty} (b : B.Elt) :
    IsPolyregularUnderRepr (fun _ : A.Elt => b) :=
  (isRegularUnderRepr_const b).isPolyregularUnderRepr

/-! ## Some regular functions between types that the constructions below use -/

/-- Swapping the two components of a pair is regular under string representation. -/
theorem isRegularUnderRepr_swap (A B : Ty) :
    IsRegularUnderRepr (A := .prod A B) (B := .prod B A) (fun x => (x.2, x.1)) :=
  IsRegularUnderRepr.pair (isRegularUnderRepr_snd A B) (isRegularUnderRepr_fst A B)

/-- Distributivity on the left, `(A₁ + A₂) × B → A₁ × B + A₂ × B`. -/
theorem isRegularUnderRepr_distrLeft (A₁ A₂ B : Ty) :
    IsRegularUnderRepr (A := .prod (.sum A₁ A₂) B) (B := .sum (.prod A₁ B) (.prod A₂ B))
      (fun x => Sum.elim (fun a => Sum.inl (a, x.2)) (fun a => Sum.inr (a, x.2)) x.1) := by
  refine (((isRegularUnderRepr_swap (.sum A₁ A₂) B).comp
    (isRegularUnderRepr_distr B A₁ A₂)).comp
    (IsRegularUnderRepr.sumMap (isRegularUnderRepr_swap B A₁)
      (isRegularUnderRepr_swap B A₂))).congr (fun x => ?_)
  obtain ⟨y, b⟩ := x
  cases y <;> rfl

/-- The singleton list, `A → A*`. -/
theorem isRegularUnderRepr_singleton (A : Ty) :
    IsRegularUnderRepr (A := A) (B := .list A) (fun a => [a]) := by
  refine ((IsRegularUnderRepr.pair (isRegularUnderRepr_id A)
    (isRegularUnderRepr_const (B := .list A) [])).comp
    ((isRegularUnderRepr_inr .one (.prod A (.list A))).comp
      (isRegularUnderRepr_cons A))).congr (fun a => rfl)

/-- The head of a list, as an element of `1 + A`. -/
theorem isRegularUnderRepr_head (A : Ty) :
    IsRegularUnderRepr (A := .list A) (B := .sum .one A)
      (fun l => match l with | [] => Sum.inl () | a :: _ => Sum.inr a) := by
  refine ((isRegularUnderRepr_uncons A).comp
    (IsRegularUnderRepr.sumMap (isRegularUnderRepr_id .one)
      (isRegularUnderRepr_fst A (.list A)))).congr (fun l => ?_)
  cases l <;> rfl

/-- The tail of a list. -/
theorem isRegularUnderRepr_tail (A : Ty) :
    IsRegularUnderRepr (A := .list A) (B := .list A) (fun l => l.tail) := by
  refine ((isRegularUnderRepr_uncons A).comp
    (IsRegularUnderRepr.copair (isRegularUnderRepr_const (A := .one) (B := .list A) [])
      (isRegularUnderRepr_snd A (.list A)))).congr (fun l => ?_)
  cases l <;> rfl

/-- The test whether a list is empty, as an element of `1 + 1`. -/
theorem isRegularUnderRepr_isEmpty (A : Ty) :
    IsRegularUnderRepr (A := .list A) (B := .sum .one .one)
      (fun l => match l with | [] => Sum.inl () | _ :: _ => Sum.inr ()) := by
  refine ((isRegularUnderRepr_head A).comp
    (IsRegularUnderRepr.sumMap (isRegularUnderRepr_id .one)
      (isRegularUnderRepr_const (A := A) (B := .one) ()))).congr (fun l => ?_)
  cases l <;> rfl

/-! ## Case distinction driven by a polyregular tag -/

open scoped Classical in
/-- Splitting the input according to a polyregular tag: if the tag says `L`, the input is placed on
the left of `P + P`, and otherwise on the right. -/
theorem isPolyregularUnderRepr_tagSplit {P : Ty} {t : P.Elt → Unit ⊕ Unit}
    (ht : IsPolyregularUnderRepr (A := P) (B := .sum .one .one) t) :
    IsPolyregularUnderRepr (A := P) (B := .sum P P)
      (fun p => Sum.elim (fun _ => Sum.inl p) (fun _ => Sum.inr p) (t p)) := by
  classical
  obtain ⟨t', ht', hte⟩ := ht
  have hhead : IsPolyregular (fun w : List Sym8 =>
      if w ∈ headLang Sym8.left then [Sym8.left] else [Sym8.right]) :=
    isPolyregular_cond
      (IsPolyregular.of_regular (IsRegularFun.of_rational (isRationalFun_const _)))
      (IsPolyregular.of_regular (IsRegularFun.of_rational (isRationalFun_const _)))
      (headLang_isRegular _)
  refine ⟨fun w => (if t' w ∈ headLang Sym8.left then [Sym8.left] else [Sym8.right]) ++ w,
    isPolyregular_concat (ht'.comp' hhead (fun _ => rfl)) isPolyregular_id, fun p => ?_⟩
  have h := hte p
  cases hp : t p with
  | inl u =>
      have : t' (P.repr p) = Sym8.left :: [Sym8.one] := by rw [h, hp]; rfl
      simp only [this, hp]
      have hmem : (Sym8.left :: [Sym8.one]) ∈ headLang Sym8.left := rfl
      rw [if_pos hmem]
      rfl
  | inr u =>
      have : t' (P.repr p) = Sym8.right :: [Sym8.one] := by rw [h, hp]; rfl
      simp only [this, hp]
      have hmem : (Sym8.right :: [Sym8.one]) ∉ headLang Sym8.left := by
        intro hc
        exact absurd (congrArg (fun o => o) hc) (by simp)
      rw [if_neg hmem]
      rfl

/-- **Case distinction driven by a polyregular tag.**  If the tag `t : P → 1 + 1` and the two
branches are polyregular under string representation, then so is the function that runs the branch
selected by the tag. -/
theorem IsPolyregularUnderRepr.cond {P C : Ty} {t : P.Elt → Unit ⊕ Unit} {u v : P.Elt → C.Elt}
    (ht : IsPolyregularUnderRepr (A := P) (B := .sum .one .one) t)
    (hu : IsPolyregularUnderRepr u) (hv : IsPolyregularUnderRepr v) :
    IsPolyregularUnderRepr (fun p => Sum.elim (fun _ => u p) (fun _ => v p) (t p)) := by
  refine ((isPolyregularUnderRepr_tagSplit ht).comp
    (IsPolyregularUnderRepr.copair hu hv)).congr (fun p => ?_)
  cases t p <;> rfl

/-! ## Distributing a parameter over a list -/

section Dup

variable (P Q : Ty)

/-- The pair `(p, l)` encoded as the list `L p :: (map R l)` over the type `P + Q`. -/
private def dupEnc (x : (Ty.prod P (.list Q)).Elt) : List (Ty.sum P Q).Elt :=
  Sum.inl x.1 :: x.2.map Sum.inr

private theorem isRegularUnderRepr_dupEnc :
    IsRegularUnderRepr (A := .prod P (.list Q)) (B := .list (.sum P Q)) (dupEnc P Q) := by
  refine ((IsRegularUnderRepr.pair
      ((isRegularUnderRepr_fst P (.list Q)).comp (isRegularUnderRepr_inl P Q))
      ((isRegularUnderRepr_snd P (.list Q)).comp
        (IsRegularUnderRepr.mapList (isRegularUnderRepr_inr P Q)))).comp
    ((isRegularUnderRepr_inr .one (.prod (.sum P Q) (.list (.sum P Q)))).comp
      (isRegularUnderRepr_cons (.sum P Q)))).congr (fun x => rfl)

/-- From a cut of the encoded list, the pair `(p, q)` when the prefix begins with `L p` and the
suffix begins with `R q`, and nothing otherwise. -/
private def dupPick (x : (Ty.prod (.list (.sum P Q)) (.list (.sum P Q))).Elt) :
    List (P.Elt × Q.Elt) :=
  match x.1, x.2 with
  | Sum.inl p :: _, Sum.inr q :: _ => [(p, q)]
  | _, _ => []

private theorem isRegularUnderRepr_dupPick :
    IsRegularUnderRepr (A := .prod (.list (.sum P Q)) (.list (.sum P Q)))
      (B := .list (.prod P Q)) (dupPick P Q) := by
  -- the head of the prefix, as an element of `1 + P`, and the head of the suffix, as `1 + Q`
  have h1 : IsRegularUnderRepr (A := .list (.sum P Q)) (B := .sum .one P)
      (fun l => match l with | Sum.inl p :: _ => Sum.inr p | _ => Sum.inl ()) := by
    refine ((isRegularUnderRepr_head (.sum P Q)).comp
      (IsRegularUnderRepr.copair (isRegularUnderRepr_inl .one P)
        (IsRegularUnderRepr.copair (isRegularUnderRepr_inr .one P)
          (isRegularUnderRepr_const (A := Q) (B := .sum .one P) (Sum.inl ()))))).congr
      (fun l => ?_)
    match l with
    | [] => rfl
    | Sum.inl p :: _ => rfl
    | Sum.inr q :: _ => rfl
  have h2 : IsRegularUnderRepr (A := .list (.sum P Q)) (B := .sum .one Q)
      (fun l => match l with | Sum.inr q :: _ => Sum.inr q | _ => Sum.inl ()) := by
    refine ((isRegularUnderRepr_head (.sum P Q)).comp
      (IsRegularUnderRepr.copair (isRegularUnderRepr_inl .one Q)
        (IsRegularUnderRepr.copair
          (isRegularUnderRepr_const (A := P) (B := .sum .one Q) (Sum.inl ()))
          (isRegularUnderRepr_inr .one Q)))).congr (fun l => ?_)
    match l with
    | [] => rfl
    | Sum.inl p :: _ => rfl
    | Sum.inr q :: _ => rfl
  -- the pair of the two heads
  have hpair : IsRegularUnderRepr (A := .prod (.list (.sum P Q)) (.list (.sum P Q)))
      (B := .prod (.sum .one P) (.sum .one Q))
      (fun x => ((match x.1 with | Sum.inl p :: _ => Sum.inr p | _ => Sum.inl ()),
        (match x.2 with | Sum.inr q :: _ => Sum.inr q | _ => Sum.inl ()))) :=
    IsRegularUnderRepr.pair
      ((isRegularUnderRepr_fst (.list (.sum P Q)) (.list (.sum P Q))).comp h1)
      ((isRegularUnderRepr_snd (.list (.sum P Q)) (.list (.sum P Q))).comp h2)
  -- the pairing of two options
  have hopt : IsRegularUnderRepr (A := .prod (.sum .one P) (.sum .one Q))
      (B := .list (.prod P Q))
      (fun x => match x.1, x.2 with
        | Sum.inr p, Sum.inr q => [(p, q)]
        | _, _ => []) := by
    have hinner : IsRegularUnderRepr (A := .prod P (.sum .one Q)) (B := .list (.prod P Q))
        (fun x => match x.2 with | Sum.inr q => [(x.1, q)] | _ => []) := by
      refine ((isRegularUnderRepr_distr P .one Q).comp
        (IsRegularUnderRepr.copair
          (isRegularUnderRepr_const (A := .prod P .one) (B := .list (.prod P Q)) [])
          (isRegularUnderRepr_singleton (.prod P Q)))).congr (fun x => ?_)
      obtain ⟨p, y⟩ := x
      cases y <;> rfl
    refine ((isRegularUnderRepr_distrLeft .one P (.sum .one Q)).comp
      (IsRegularUnderRepr.copair
        (isRegularUnderRepr_const (A := .prod .one (.sum .one Q)) (B := .list (.prod P Q)) [])
        hinner)).congr (fun x => ?_)
    obtain ⟨y, z⟩ := x
    cases y <;> cases z <;> rfl
  refine (hpair.comp hopt).congr (fun x => ?_)
  obtain ⟨l₁, l₂⟩ := x
  match l₁, l₂ with
  | [], _ => rfl
  | Sum.inl p :: _, [] => rfl
  | Sum.inl p :: _, Sum.inl p' :: _ => rfl
  | Sum.inl p :: _, Sum.inr q :: _ => rfl
  | Sum.inr q :: _, _ => rfl

/-- Only the first entry of the prefix matters. -/
private theorem dupPick_cons_inl (p : P.Elt) (x : (Ty.sum P Q).Elt)
    (u v : List (Ty.sum P Q).Elt) :
    dupPick P Q (Sum.inl p :: x :: u, v) = dupPick P Q (Sum.inl p :: u, v) := by
  cases v with
  | nil => rfl
  | cons y v => cases y <;> rfl

/-- Splitting off the first entry of a computation that runs over `0,1,…,n`. -/
private theorem flatten_range_succ {Y : Type} (h : ℕ → List Y) (n : ℕ) :
    (((List.range (n + 1)).map h).flatten)
      = h 0 ++ (((List.range n).map (fun i => h (i + 1))).flatten) := by
  rw [List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def]

/-- The combinatorial identity behind `Transducers.isPolyregularUnderRepr_dup`: the cuts of
`L p :: map R l` that have `L p` at the end of the prefix and an entry of `l` at the start of the
suffix list the entries of `l`, in order. -/
private theorem dup_flatten (p : P.Elt) (l : List Q.Elt) :
    (((List.range (l.length + 1)).map (fun i =>
        dupPick P Q (Sum.inl p :: (l.map Sum.inr).take i, (l.map Sum.inr).drop i))).flatten)
      = l.map (fun q => (p, q)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.length_cons, flatten_range_succ]
      have h0 : dupPick P Q (Sum.inl p :: ((a :: l).map Sum.inr).take 0,
          ((a :: l).map Sum.inr).drop 0) = [(p, a)] := rfl
      have hstep : (fun i : ℕ =>
            dupPick P Q (Sum.inl p :: ((a :: l).map Sum.inr).take (i + 1),
              ((a :: l).map Sum.inr).drop (i + 1)))
          = (fun i : ℕ =>
            dupPick P Q (Sum.inl p :: (l.map Sum.inr).take i, (l.map Sum.inr).drop i)) := by
        funext i
        simp only [List.map_cons, List.take_succ_cons, List.drop_succ_cons]
        exact dupPick_cons_inl P Q p (Sum.inr a) _ _
      rw [h0, hstep, ih]
      rfl

/-- **Distributing a parameter over a list is polyregular.** -/
theorem isPolyregularUnderRepr_dup :
    IsPolyregularUnderRepr (A := .prod P (.list Q)) (B := .list (.prod P Q))
      (fun x => x.2.map (fun q => (x.1, q))) := by
  refine (((isRegularUnderRepr_dupEnc P Q).isPolyregularUnderRepr.comp
    (isPolyregularUnderRepr_splitsRev (.sum P Q))).comp
    ((IsRegularUnderRepr.mapList (isRegularUnderRepr_dupPick P Q)).isPolyregularUnderRepr.comp
      (isRegularUnderRepr_concat (.prod P Q)).isPolyregularUnderRepr)).congr (fun x => ?_)
  obtain ⟨p, l⟩ := x
  show ((((splitsList (dupEnc P Q (p, l))).reverse).map (dupPick P Q)).flatten)
    = l.map (fun q => (p, q))
  rw [splitsList_reverse]
  have hlen : (dupEnc P Q (p, l)).length = l.length + 1 := by
    simp [dupEnc]
  rw [hlen]
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.flatten_cons]
  have h0 : dupPick P Q ((dupEnc P Q (p, l)).take 0, (dupEnc P Q (p, l)).drop 0) = [] := rfl
  rw [h0]
  simp only [List.nil_append, Function.comp_def]
  have hstep : ∀ i : ℕ, dupPick P Q ((dupEnc P Q (p, l)).take (i + 1),
      (dupEnc P Q (p, l)).drop (i + 1))
      = dupPick P Q (Sum.inl p :: (l.map Sum.inr).take i, (l.map Sum.inr).drop i) := by
    intro i
    simp [dupEnc]
  simp only [hstep]
  exact dup_flatten P Q p l

end Dup

/-- **Map with a parameter.**  If `ℓ : P → Q*` and `f : P × Q → R` are polyregular under string
representation, then so is `p ↦ (ℓ p).map (fun q => f (p, q))`. -/
theorem IsPolyregularUnderRepr.mapParam {P Q R : Ty} {l : P.Elt → List Q.Elt}
    {f : P.Elt × Q.Elt → R.Elt}
    (hl : IsPolyregularUnderRepr (A := P) (B := .list Q) l)
    (hf : IsPolyregularUnderRepr (A := .prod P Q) f) :
    IsPolyregularUnderRepr (A := P) (B := .list R) (fun p => (l p).map (fun q => f (p, q))) := by
  refine ((IsPolyregularUnderRepr.pair
    (isRegularUnderRepr_id P).isPolyregularUnderRepr hl).comp
    ((isPolyregularUnderRepr_dup P Q).comp
      (IsPolyregularUnderRepr.mapList hf))).congr (fun p => ?_)
  simp [Function.comp_def]

end Transducers
