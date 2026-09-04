/-
Lemma `lem:terms-define-map-reverse-duplicate` of Section *Combinators* of *Transducers*
(M. Bojańczyk): the two non-rational prime regular functions, map reverse and map duplicate, are
definable by regular terms.

Both are instances of the *map lifting* `Transducers.mapLift` of Definition `def:map-lifting`,
which applies a function to every block of a string over `A + 1` delimited by the separator.  The
book's construction is exactly the one available to a term: split the string at the separators
(the atomic term of Example `ex:split`), apply the function to the first block and to the block of
every pair, and put the string back together with the inverse of split -- the inverse being the
derived term `Transducers.tfun_unsplit` of `CombDerived.lean`.  Reversal of a block is the atomic
reverse, and duplication of a block is `(id, id); binconc`.

The bridge between the two descriptions of a block decomposition, `Transducers.splitSep` (used by
`mapLift`) and `Transducers.splitList` (the semantics of the atomic term), is
`Transducers.splitList_map_toSum` below.
-/
import RequestProject.PartC.CombStrFam
import RequestProject.PartA.MapLift
import RequestProject.PartC.MapLiftAux

namespace Transducers

/-! ## `A + 1` and `Option A` -/

/-- The separator alphabet `A + 1` read as `Option A`. -/
def ofSum {α : Type} : α ⊕ Unit → Option α
  | Sum.inl a => some a
  | Sum.inr _ => none

/-- `Option A` read as the separator alphabet `A + 1`. -/
def toSum {α : Type} : Option α → α ⊕ Unit
  | some a => Sum.inl a
  | none => Sum.inr ()

@[simp] lemma ofSum_toSum {α : Type} (o : Option α) : ofSum (toSum o) = o := by
  cases o <;> rfl

@[simp] lemma toSum_ofSum {α : Type} (s : α ⊕ Unit) : toSum (ofSum s) = s := by
  rcases s with a | u
  · rfl
  · cases u; rfl

/-- The bijection between `A + 1` and `Option A`. -/
def sumOptEquiv (α : Type) : α ⊕ Unit ≃ Option α where
  toFun := ofSum
  invFun := toSum
  left_inv := toSum_ofSum
  right_inv := ofSum_toSum

/-! ## Intercalation -/

lemma intercalate_cons {α : Type} (x : List α) :
    ∀ (y : List α) (ys : List (List α)),
      List.intercalate x (y :: ys) = y ++ (ys.map (fun z => x ++ z)).flatten := by
  intro y ys
  induction ys generalizing y with
  | nil => simp [List.intercalate]
  | cons z zs ih =>
      have h : List.intercalate x (y :: z :: zs) = y ++ x ++ List.intercalate x (z :: zs) := by
        simp [List.intercalate, List.intersperse]
      rw [h, ih z]
      simp

/-! ## The two descriptions of the block decomposition -/

lemma splitList_map_toSum {α : Type} :
    ∀ w : List (Option α),
      splitList (w.map toSum)
        = ((splitSep w).headI, (splitSep w).tail.map (fun u => ((), u))) := by
  intro w
  induction w with
  | nil => rfl
  | cons o w ih =>
      have hne := splitSep_ne_nil w
      cases o with
      | none =>
          rw [List.map_cons]
          show splitList (Sum.inr () :: w.map toSum) = _
          rw [splitList_inr, ih]
          cases hs : splitSep w with
          | nil => exact absurd hs hne
          | cons u us => simp [splitSep, hs]
      | some a =>
          rw [List.map_cons]
          show splitList (Sum.inl a :: w.map toSum) = _
          rw [splitList_inl, ih]
          cases hs : splitSep w with
          | nil => exact absurd hs hne
          | cons u us => simp [splitSep, hs]

/-- The map lifting, described with `splitList` instead of `splitSep`: this is exactly the shape
of the term. -/
lemma mapLift_eq_unsplit {α : Type} (f : List α → List α) (w : List (Option α)) :
    (mapLift f w).map toSum
      = unsplitList (f (splitList (w.map toSum)).1,
          (splitList (w.map toSum)).2.map (fun p => (p.1, f p.2))) := by
  rw [splitList_map_toSum]
  have hne := splitSep_ne_nil w
  rw [show mapLift f w
      = List.intercalate [none] ((splitSep w).map (fun v => (f v).map some)) from rfl]
  cases hs : splitSep w with
  | nil => exact absurd hs hne
  | cons u us =>
      simp only [List.headI, List.tail_cons, List.map_cons, List.map_map]
      rw [intercalate_cons]
      simp [unsplitList, List.map_map, Function.comp_def, toSum]

/-! ## The map lifting as a term -/

/-- The term that lifts a term on blocks to the whole string: split, apply, put back together. -/
theorem tfun_mapLift {A₀ : Ty} {f : List A₀.Elt → List A₀.Elt}
    (hf : IsRegularTermFun (A := .list A₀) (B := .list A₀) f) :
    IsRegularTermFun (A := .list (.sum A₀ .one)) (B := .list (.sum A₀ .one))
      (fun l => (mapLift f (l.map ofSum)).map toSum) := by
  have hmid : IsRegularTermFun
      (A := .prod (.list A₀) (.list (.prod .one (.list A₀))))
      (B := .prod (.list A₀) (.list (.prod .one (.list A₀))))
      (fun p => (f p.1, p.2.map (fun q => (q.1, f q.2)))) :=
    tfun_prodMap hf ((tfun_prodMap (tfun_id .one) hf).mapList)
  refine (((tfun_split A₀ .one).comp hmid).comp (tfun_unsplit A₀ .one)).congr ?_
  intro l
  have h := mapLift_eq_unsplit f (l.map ofSum)
  rw [List.map_map] at h
  simp only [Function.comp_def, toSum_ofSum, List.map_id'] at h
  exact h.symm

/-- The map lifting of a term-definable function on blocks is definable by terms. -/
theorem termStrFun_mapLift {T : Ty} (hT : Finite T.Elt) {f : List T.Elt → List T.Elt}
    (hf : IsRegularTermFun (A := .list T) (B := .list T) f) : TermStrFun (mapLift f) := by
  haveI := hT
  haveI : Finite (Ty.sum T Ty.one).Elt := by
    show Finite (T.Elt ⊕ Unit); infer_instance
  refine termStrFun_of_one (Ty.sum T Ty.one) (Ty.sum T Ty.one) inferInstance
    (sumOptEquiv T.Elt) (sumOptEquiv T.Elt).symm ?_
  exact tfun_mapLift hf

/-! ## The map lifting under a renaming of the alphabet -/

/-! ## Lemma `lem:terms-define-map-reverse-duplicate` -/

/-- **Lemma `lem:terms-define-map-reverse-duplicate`, map reverse.**  For every type `A₀`, the
function `map reverse` on `(A₀ + 1)*` is definable by a regular term. -/
theorem terms_define_map_reverse (A₀ : Ty) :
    IsRegularTermFun (A := .list (.sum A₀ .one)) (B := .list (.sum A₀ .one))
      (fun l => (mapReverse A₀.Elt (l.map ofSum)).map toSum) :=
  tfun_mapLift (tfun_reverse A₀)

/-- **Lemma `lem:terms-define-map-reverse-duplicate`, map duplicate.**  For every type `A₀`, the
function `map duplicate` on `(A₀ + 1)*` is definable by a regular term. -/
theorem terms_define_map_duplicate (A₀ : Ty) :
    IsRegularTermFun (A := .list (.sum A₀ .one)) (B := .list (.sum A₀ .one))
      (fun l => (mapDuplicate A₀.Elt (l.map ofSum)).map toSum) :=
  tfun_mapLift (((tfun_id (.list A₀)).pair (tfun_id (.list A₀))).comp (tfun_append A₀))

/-- A letter-to-letter renaming is definable by terms. -/
lemma termStrFun_mapRen {X Y : Type} (h : X → Y) : TermStrFun (fun w : List X => w.map h) :=
  (termStrFun_homOf (fun a => [h a])).congr (fun w => by
    induction w with
    | nil => rfl
    | cons a w ih => simpa [homOf] using congrArg (fun z => h a :: z) ih)

/-- On an empty alphabet the map lifting is the identity: every letter is the separator. -/
lemma mapLift_of_isEmpty {α : Type} [IsEmpty α] {f : List α → List α} (hf : f [] = []) :
    ∀ w : List (Option α), mapLift f w = w := by
  intro w
  induction w with
  | nil => simp [mapLift, splitSep, hf, List.intercalate]
  | cons o w ih =>
      cases o with
      | none =>
          show List.intercalate [none] ((splitSep (none :: w)).map (fun v => (f v).map some)) = _
          rw [show splitSep (none :: w) = [] :: splitSep w from rfl, List.map_cons,
            intercalate_cons, hf]
          have h : List.intercalate ([none] : List (Option α))
              ((splitSep w).map (fun v => (f v).map some)) = w := ih
          have hne := splitSep_ne_nil w
          cases hs : splitSep w with
          | nil => exact absurd hs hne
          | cons u us =>
              rw [hs, List.map_cons, intercalate_cons] at h
              simpa using congrArg (fun z => (none : Option α) :: z) h
      | some a => exact (IsEmpty.false a).elim

/-- **The two non-rational primes of `Transducers.RegularFam` are definable by terms.**  The
statement is uniform in the function applied to each block: it is used for `List.reverse` and for
`fun u => u ++ u`. -/
theorem termStrFun_of_mapLiftPrime {X Y A₀ : Type} (hX : Finite X)
    (e : X ≃ Option A₀) (e' : Y ≃ Option A₀)
    (f : ∀ α : Type, List α → List α)
    (hf0 : ∀ α : Type, f α [] = [])
    (hfnat : ∀ {α β : Type} (k : α → β) (u : List α), f β (u.map k) = (f α u).map k)
    (hfT : ∀ T : Ty, IsRegularTermFun (A := .list T) (B := .list T) (f T.Elt))
    {g : List X → List Y} (hg : ∀ w, g w = (mapLift (f A₀) (w.map e)).map e'.symm) :
    TermStrFun g := by
  haveI := hX
  haveI : Finite A₀ := Finite.of_injective (fun a : A₀ => e.symm (some a)) (by
    intro a b hab
    exact Option.some.inj (by simpa using congrArg e hab))
  by_cases hne : Nonempty A₀
  · haveI := hne
    obtain ⟨T, ⟨eT⟩, hTf⟩ := exists_ty_equiv A₀
    haveI := hTf
    have hcomm : ∀ v : List (Option A₀),
        mapLift (f T.Elt) (v.map (Option.map eT)) = (mapLift (f A₀) v).map (Option.map eT) :=
      mapLift_map_optionMap eT (fun u => hfnat eT u)
    have hg' : ∀ w : List X,
        g w = ((mapLift (f T.Elt) (w.map (fun a => (e a).map eT))).map
          (fun o => e'.symm (o.map eT.symm))) := by
      intro w
      rw [hg]
      have h1 : w.map (fun a => (e a).map eT) = (w.map e).map (Option.map eT) := by
        simp [List.map_map, Function.comp_def]
      rw [h1, hcomm, List.map_map]
      refine congrArg (fun (h : Option A₀ → Y) => (mapLift (f A₀) (w.map e)).map h) ?_
      funext o
      cases o <;> simp
    refine ((((termStrFun_mapRen (fun a : X => (e a).map eT)).comp
      (termStrFun_mapLift hTf (hfT T))).comp
      (termStrFun_mapRen (fun o : Option T.Elt => e'.symm (o.map eT.symm)))).congr ?_)
    intro w
    exact (hg' w).symm
  · haveI : IsEmpty A₀ := not_nonempty_iff.1 hne
    refine (termStrFun_mapRen (fun a : X => e'.symm (e a))).congr ?_
    intro w
    rw [hg, mapLift_of_isEmpty (hf0 A₀), List.map_map]
    rfl

end Transducers
