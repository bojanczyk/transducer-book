/-
Part D: the map lifting of a polyregular function is polyregular.

The map lifting `Transducers.mapLift f` of Definition `def:map-lifting` applies `f` to every block
of its input, the blocks being delimited by a fresh separator.  Lemma
`lem:regular-closure-properties` says that the map lifting of a *regular* function is regular
(`Transducers.isRegularFun_mapLift`); this file proves the same for the polyregular functions,
which is what the combinator `f*` of Definition `def:polyregular-terms` needs.

The proof is the obvious induction on the definition of a polyregular function as a composition of
primes: the map lifting commutes with composition (`Transducers.mapLift_comp'`), the map lifting of
a regular function is regular, and so the only thing to prove is that the map lifting of marked
squaring is polyregular.  That is the content of
`Transducers.isPolyregular_mapLift_markedSquare`, and it is where the construction of
`RequestProject/PartD/PolyPerSplit.lean` is used: the marked square of every block at once is
obtained by running over all the ways of cutting the *whole* input into a prefix and a suffix, and
keeping, for each cut, only the block in which the cut falls.
-/
import RequestProject.PartD.PolyPerSplit
import RequestProject.PartC.RegClosure
import RequestProject.PartC.RegAut
import RequestProject.PartC.CombMark

namespace Transducers

/-! ## The map lifting of marked squaring -/

namespace MSLift

variable {A : Type}

/-- The alphabet of the copies: a letter of the input, underlined (`Sum.inl`) or not. -/
abbrev Lt (A : Type) : Type := Option A ⊕ Option A

/-! ### Taking the longest prefix of the letters that satisfy a predicate -/

section TakeWhile

variable {Gam : Type}

/-- The state of the sequential rewriting computing `List.takeWhile`: has a letter failing the
predicate been read? -/
def twStep (p : Gam → Bool) : Bool → Gam → Bool := fun b x => b || !p x

/-- The output of the sequential rewriting computing `List.takeWhile`. -/
def twOut (p : Gam → Bool) : Bool → Gam → List Gam := fun b x => if b || !p x then [] else [x]

lemma seqEval_tw (p : Gam → Bool) :
    ∀ (c : List Gam) (b : Bool),
      seqEval (twStep p) (twOut p) b c = if b then [] else c.takeWhile p := by
  intro c
  induction c with
  | nil => intro b; cases b <;> simp
  | cons x c ih =>
      intro b
      cases b with
      | true => simp [twStep, twOut, ih]
      | false =>
          by_cases hx : p x = true
          · simp [twStep, twOut, hx, ih]
          · simp only [Bool.not_eq_true] at hx
            simp [twStep, twOut, hx, ih]

/-- Taking the longest prefix of the letters satisfying a predicate is a regular function. -/
lemma isRegularFun_takeWhile [Finite Gam] (p : Gam → Bool) :
    IsRegularFun (fun c : List Gam => c.takeWhile p) :=
  (IsRegularFun.of_rational (isRationalFun_seqEval (twStep p) false (twOut p))).congr
    (fun c => by rw [seqEval_tw]; simp)

lemma takeWhile_append_of_all (p : Gam → Bool) (X Y : List Gam) (h : ∀ x ∈ X, p x = true) :
    (X ++ Y).takeWhile p = X ++ Y.takeWhile p := by
  induction X with
  | nil => simp
  | cons x X ih =>
      have hx : p x = true := h x (by simp)
      have hX : ∀ y ∈ X, p y = true := fun y hy => h y (by simp [hy])
      simp [hx, ih hX]

end TakeWhile

/-! ### The function applied to every copy -/

/-- Is the letter an underlined separator? -/
def isInlSep : Lt A → Bool
  | Sum.inl none => true
  | _ => false

/-- Is the letter a separator that is not underlined? -/
def isInrSep : Lt A → Bool
  | Sum.inr none => true
  | _ => false

/-- The part of a copy that lies strictly between the last underlined separator and the first
separator that is not underlined: the block of the input in which the cut falls. -/
def segOf (c : List (Lt A)) : List (Lt A) :=
  (((c.reverse).takeWhile (fun x => !isInlSep x)).reverse).takeWhile (fun x => !isInrSep x)

/-- Reading off a letter of that block: the separators have been removed already. -/
def relab : Lt A → List (Option (A ⊕ A))
  | Sum.inl (some a) => [some (Sum.inl a)]
  | Sum.inr (some a) => [some (Sum.inr a)]
  | _ => []

/-- The state remembering the kind of the last underlined letter: `none` if there is none,
`some true` if it is a separator and `some false` if it is a letter of the input. -/
def lastStep : Option Bool → Lt A → Option Bool
  | _, Sum.inl none => some true
  | _, Sum.inl (some _) => some false
  | s, Sum.inr _ => s

/-- The copies whose last underlined letter is a separator (`b = true`) or a letter of the input
(`b = false`). -/
def lastLang (A : Type) (b : Bool) : Language (Lt A) := {c | c.foldl lastStep none = some b}

lemma isRegular_lastLang [Finite A] (b : Bool) : (lastLang A b).IsRegular :=
  RegAut.isRegular_foldl lastStep none {s | s = some b}

open scoped Classical in
/-- The function that is applied to every copy in the construction of the map lifting of marked
squaring: nothing if no letter is underlined; the separator if the last underlined letter is a
separator; and otherwise the block in which the last underlined letter lies, with its
underlining. -/
noncomputable def msPer (c : List (Lt A)) : List (Option (A ⊕ A)) :=
  if c ∈ lastLang A false then homOf relab (segOf c)
  else if c ∈ lastLang A true then [none] else []

lemma msPer_nil : msPer ([] : List (Lt A)) = [] := by
  classical
  have h1 : ([] : List (Lt A)) ∉ lastLang A false := by
    show ¬ (List.foldl lastStep none ([] : List (Lt A)) = some false)
    simp
  have h2 : ([] : List (Lt A)) ∉ lastLang A true := by
    show ¬ (List.foldl lastStep none ([] : List (Lt A)) = some true)
    simp
  simp [msPer, h1, h2]

lemma isRegularFun_msPer [Finite A] : IsRegularFun (msPer : List (Lt A) → List (Option (A ⊕ A))) := by
  classical
  haveI : Finite (Lt A) := inferInstance
  haveI : Finite (Option (A ⊕ A)) := inferInstance
  have hseg : IsRegularFun (fun c : List (Lt A) => homOf relab (segOf c)) := by
    have h1 : IsRegularFun (fun c : List (Lt A) => c.reverse) := Comb.isRegularFun_listReverse (Lt A)
    have h2 : IsRegularFun (fun c : List (Lt A) => c.takeWhile (fun x => !isInlSep x)) :=
      isRegularFun_takeWhile _
    have h3 : IsRegularFun (fun c : List (Lt A) => c.takeWhile (fun x => !isInrSep x)) :=
      isRegularFun_takeWhile _
    have h4 : IsRegularFun (homOf (relab : Lt A → List (Option (A ⊕ A)))) :=
      IsRegularFun.of_rational (isRationalFun_homOf _)
    exact ((((h1.comp' h2 (fun _ => rfl)).comp' h1 (fun _ => rfl)).comp'
      h3 (fun _ => rfl)).comp' h4 (fun _ => rfl)).congr (fun _ => rfl)
  have hsep : IsRegularFun (fun _ : List (Lt A) => [(none : Option (A ⊕ A))]) :=
    IsRegularFun.of_rational (isRationalFun_const _)
  have hnil : IsRegularFun (fun _ : List (Lt A) => ([] : List (Option (A ⊕ A)))) :=
    IsRegularFun.of_rational (isRationalFun_const _)
  exact isRegularFun_cond hseg (isRegularFun_cond hsep hnil (isRegular_lastLang true))
    (isRegular_lastLang false)

/-! ### What the function computes on a copy -/

/-- The state of the underlined prefix: `none` if the prefix is empty, and otherwise the letters
of its last block, that is, the letters after its last separator. -/
def stStep : Option (List A) → Option A → Option (List A)
  | _, none => some []
  | s, some a => some ((s.getD []) ++ [a])

/-- The state of an underlined prefix. -/
def stOf (P : List (Option A)) : Option (List A) := P.foldl stStep none

@[simp] lemma stOf_nil : stOf ([] : List (Option A)) = none := rfl

lemma stOf_append_singleton (P : List (Option A)) (x : Option A) :
    stOf (P ++ [x]) = stStep (stOf P) x := by
  simp [stOf]

/-- The letters of the first block of a string. -/
def firstBlk : List (Option A) → List A
  | [] => []
  | none :: _ => []
  | some a :: w => a :: firstBlk w

lemma firstBlk_of_splitSep :
    ∀ (w : List (Option A)) (c₀ : List A) (cs : List (List A)),
      splitSep w = c₀ :: cs → firstBlk w = c₀ := by
  intro w
  induction w with
  | nil => intro c₀ cs h; simp [splitSep] at h; simp [firstBlk, h.1]
  | cons x w ih =>
      cases x with
      | none => intro c₀ cs h; simp [splitSep] at h; simp [firstBlk, h.1]
      | some a =>
          intro c₀ cs h
          cases hw : splitSep w with
          | nil => exact absurd hw (splitSep_ne_nil w)
          | cons u us =>
              rw [show splitSep (some a :: w) = (a :: u) :: us by rw [splitSep, hw]] at h
              have h1 : c₀ = a :: u := (List.cons.inj h).1.symm
              simp [firstBlk, ih u us hw, h1]

/-- The value of the function on a copy, as a function of the state of the underlined prefix and
of the part of the input that is not underlined. -/
def msOut (s : Option (List A)) (S : List (Option A)) : List (Option (A ⊕ A)) :=
  match s with
  | none => []
  | some q =>
      if q = [] then [none]
      else q.map (fun a => some (Sum.inl a)) ++ (firstBlk S).map (fun a => some (Sum.inr a))

lemma foldl_lastStep_inr (S : List (Option A)) (s : Option Bool) :
    (S.map Sum.inr).foldl lastStep s = s := by
  induction S generalizing s with
  | nil => rfl
  | cons x S ih => simpa [lastStep] using ih s

lemma foldl_lastStep_inl :
    ∀ (P : List (Option A)) (s : Option (List A)),
      (P.map Sum.inl).foldl lastStep (s.map (fun q => q.isEmpty))
        = (P.foldl stStep s).map (fun q => q.isEmpty) := by
  intro P
  induction P with
  | nil => intro s; rfl
  | cons x P ih =>
      intro s
      cases x with
      | none =>
          have : lastStep (s.map (fun q : List A => q.isEmpty)) (Sum.inl none : Lt A)
              = (stStep s none).map (fun q : List A => q.isEmpty) := by
            simp [lastStep, stStep]
          simpa [this] using ih (stStep s none)
      | some a =>
          have : lastStep (s.map (fun q : List A => q.isEmpty)) (Sum.inl (some a) : Lt A)
              = (stStep s (some a)).map (fun q : List A => q.isEmpty) := by
            simp [lastStep, stStep]
          simpa [this] using ih (stStep s (some a))

lemma foldl_lastStep_copy (P S : List (Option A)) :
    (P.map Sum.inl ++ S.map Sum.inr).foldl lastStep none
      = (stOf P).map (fun q => q.isEmpty) := by
  rw [List.foldl_append, foldl_lastStep_inr]
  exact foldl_lastStep_inl P none

lemma takeWhile_inl_reverse :
    ∀ P : List (Option A),
      ((P.map Sum.inl).reverse.takeWhile (fun x => !isInlSep x))
        = (((stOf P).getD []).map (fun a => Sum.inl (some a) : A → Lt A)).reverse := by
  intro P
  induction P using List.reverseRecOn with
  | nil => rfl
  | append_singleton P x ih =>
      cases x with
      | none =>
          rw [stOf_append_singleton]
          simp [List.map_append, isInlSep, stStep]
      | some a =>
          rw [stOf_append_singleton]
          have : ((P ++ [some a]).map (Sum.inl : Option A → Lt A)).reverse
              = Sum.inl (some a) :: (P.map Sum.inl).reverse := by simp
          rw [this, List.takeWhile_cons, ih]
          simp [isInlSep, stStep]

lemma takeWhile_inr :
    ∀ S : List (Option A),
      ((S.map Sum.inr).takeWhile (fun x => !isInrSep x))
        = (firstBlk S).map (fun a => Sum.inr (some a) : A → Lt A) := by
  intro S
  induction S with
  | nil => rfl
  | cons x S ih =>
      cases x with
      | none => simp [isInrSep, firstBlk]
      | some a => simpa [isInrSep, firstBlk] using ih

lemma segOf_copy (P S : List (Option A)) :
    segOf (P.map Sum.inl ++ S.map Sum.inr)
      = ((stOf P).getD []).map (fun a => Sum.inl (some a) : A → Lt A)
        ++ (firstBlk S).map (fun a => Sum.inr (some a) : A → Lt A) := by
  have hall : ∀ x ∈ (S.map (Sum.inr : Option A → Lt A)).reverse, (!isInlSep x) = true := by
    intro x hx
    simp only [List.mem_reverse, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    simp [isInlSep]
  have h1 : (P.map (Sum.inl : Option A → Lt A) ++ S.map Sum.inr).reverse
      = (S.map (Sum.inr : Option A → Lt A)).reverse ++ (P.map Sum.inl).reverse := by
    simp
  rw [segOf, h1, takeWhile_append_of_all _ _ _ hall, takeWhile_inl_reverse,
    List.reverse_append, List.reverse_reverse, List.reverse_reverse]
  have hall2 : ∀ x ∈ ((stOf P).getD []).map (fun a => Sum.inl (some a) : A → Lt A),
      (!isInrSep x) = true := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    simp [isInrSep]
  rw [takeWhile_append_of_all _ _ _ hall2, takeWhile_inr]

lemma homOf_relab_seg (Q R : List A) :
    homOf relab (Q.map (fun a => Sum.inl (some a) : A → Lt A)
        ++ R.map (fun a => Sum.inr (some a) : A → Lt A))
      = Q.map (fun a => some (Sum.inl a)) ++ R.map (fun a => some (Sum.inr a)) := by
  have hQ : ∀ Q : List A, homOf relab (Q.map (fun a => Sum.inl (some a) : A → Lt A))
      = Q.map (fun a => some (Sum.inl a)) := by
    intro Q
    induction Q with
    | nil => rfl
    | cons a Q ih => simpa [homOf, relab] using ih
  have hR : ∀ R : List A, homOf relab (R.map (fun a => Sum.inr (some a) : A → Lt A))
      = R.map (fun a => some (Sum.inr a)) := by
    intro R
    induction R with
    | nil => rfl
    | cons a R ih => simpa [homOf, relab] using ih
  simp only [homOf, List.map_append, List.flatten_append] at *
  rw [hQ, hR]

lemma msPer_copy (P S : List (Option A)) :
    msPer (P.map Sum.inl ++ S.map Sum.inr) = msOut (stOf P) S := by
  classical
  have hfold := foldl_lastStep_copy P S
  cases hP : stOf P with
  | none =>
      have h1 : (P.map Sum.inl ++ S.map Sum.inr) ∉ lastLang A false := by
        show ¬ (List.foldl lastStep none (P.map Sum.inl ++ S.map Sum.inr) = some false)
        rw [hfold, hP]; simp
      have h2 : (P.map Sum.inl ++ S.map Sum.inr) ∉ lastLang A true := by
        show ¬ (List.foldl lastStep none (P.map Sum.inl ++ S.map Sum.inr) = some true)
        rw [hfold, hP]; simp
      simp [msPer, h1, h2, msOut]
  | some q =>
      by_cases hq : q = []
      · subst hq
        have h1 : (P.map Sum.inl ++ S.map Sum.inr) ∉ lastLang A false := by
          show ¬ (List.foldl lastStep none (P.map Sum.inl ++ S.map Sum.inr) = some false)
          rw [hfold, hP]; simp
        have h2 : (P.map Sum.inl ++ S.map Sum.inr) ∈ lastLang A true := by
          show List.foldl lastStep none (P.map Sum.inl ++ S.map Sum.inr) = some true
          rw [hfold, hP]; simp
        simp [msPer, h1, h2, msOut]
      · have hne : q.isEmpty = false := by
          cases q with
          | nil => exact absurd rfl hq
          | cons _ _ => rfl
        have h1 : (P.map Sum.inl ++ S.map Sum.inr) ∈ lastLang A false := by
          show List.foldl lastStep none (P.map Sum.inl ++ S.map Sum.inr) = some false
          rw [hfold, hP]; simp [hne]
        rw [msPer, if_pos h1, segOf_copy, homOf_relab_seg, msOut, hP]
        simp [hq]

/-! ### The computation over all the cuts -/

lemma perSplitFrom_msPer :
    ∀ (v : List (Option A)) (P : List (Option A)) (b₀ : List A) (bs : List (List A)),
      splitSep v = b₀ :: bs →
      perSplitFrom msPer P v
        = msOut (stOf P) v
          ++ blockStr (msBlocks ((stOf P).getD []) b₀ :: bs.map (markedSquare A)) := by
  intro v
  induction v with
  | nil =>
      intro P b₀ bs h
      have hb : b₀ = [] ∧ bs = [] := by
        rw [show splitSep ([] : List (Option A)) = [[]] from rfl] at h
        exact ⟨((List.cons.inj h).1).symm, ((List.cons.inj h).2).symm⟩
      obtain ⟨rfl, rfl⟩ := hb
      rw [perSplitFrom_nil, show P.map (Sum.inl : Option A → Lt A)
        = P.map Sum.inl ++ ([] : List (Option A)).map Sum.inr by simp, msPer_copy]
      simp
  | cons x w ih =>
      intro P b₀ bs h
      obtain ⟨c₀, cs, hw⟩ : ∃ c₀ cs, splitSep w = c₀ :: cs := by
        cases hw : splitSep w with
        | nil => exact absurd hw (splitSep_ne_nil w)
        | cons c₀ cs => exact ⟨c₀, cs, rfl⟩
      rw [perSplitFrom_cons, msPer_copy, ih (P ++ [x]) c₀ cs hw, stOf_append_singleton]
      cases x with
      | none =>
          have hb : b₀ = [] ∧ bs = c₀ :: cs := by
            rw [show splitSep ((none : Option A) :: w) = [] :: splitSep w from rfl, hw] at h
            exact ⟨((List.cons.inj h).1).symm, ((List.cons.inj h).2).symm⟩
          obtain ⟨rfl, rfl⟩ := hb
          rw [show stStep (stOf P) none = some ([] : List A) from rfl]
          rw [show msOut (some ([] : List A)) w = [(none : Option (A ⊕ A))] from by simp [msOut]]
          rw [show ((some ([] : List A)).getD []) = ([] : List A) from rfl]
          rw [msBlocks_nil, List.map_cons, markedSquare_eq_msBlocks c₀,
            blockStr_cons ([] : List (A ⊕ A))
              (msBlocks ([] : List A) c₀ :: cs.map (markedSquare A)) (by simp)]
          simp
      | some a =>
          have hb : b₀ = a :: c₀ ∧ bs = cs := by
            rw [show splitSep ((some a) :: w) = (a :: c₀) :: cs by rw [splitSep, hw]] at h
            exact ⟨((List.cons.inj h).1).symm, ((List.cons.inj h).2).symm⟩
          obtain ⟨rfl, rfl⟩ := hb
          have hstep : stStep (stOf P) (some a) = some (((stOf P).getD []) ++ [a]) := rfl
          rw [hstep]
          have hne : (((stOf P).getD []) ++ [a]) ≠ [] := by simp
          rw [show msOut (some (((stOf P).getD []) ++ [a])) w
            = (((stOf P).getD []) ++ [a]).map (fun a => some (Sum.inl a))
              ++ (firstBlk w).map (fun a => some (Sum.inr a)) from by simp [msOut, hne]]
          rw [firstBlk_of_splitSep w c₀ bs hw]
          rw [show ((some (((stOf P).getD []) ++ [a])).getD []) = ((stOf P).getD []) ++ [a] from rfl]
          rw [msBlocks_cons]
          rw [blockStr_cons_append ((((stOf P).getD []) ++ [a]).map Sum.inl ++ c₀.map Sum.inr)
            (msBlocks (((stOf P).getD []) ++ [a]) c₀) (bs.map (markedSquare A))]
          simp [List.map_map, Function.comp_def, List.append_assoc]

end MSLift

open MSLift in
/-- **The map lifting of marked squaring is polyregular.** -/
theorem isPolyregular_mapLift_markedSquare (A : Type) [Finite A] :
    IsPolyregular (mapLift (markedSquare A)) := by
  haveI : Finite (Option A) := inferInstance
  haveI : Finite (Option (A ⊕ A)) := inferInstance
  refine (isPolyregular_perSplit (X := Option A) isRegularFun_msPer msPer_nil).congr (fun v => ?_)
  obtain ⟨b₀, bs, hv⟩ : ∃ b₀ bs, splitSep v = b₀ :: bs := by
    cases hv : splitSep v with
    | nil => exact absurd hv (splitSep_ne_nil v)
    | cons b₀ bs => exact ⟨b₀, bs, rfl⟩
  rw [perSplit_eq_perSplitFrom, perSplitFrom_msPer v [] b₀ bs hv]
  rw [stOf_nil, show msOut (A := A) none v = [] from rfl,
    show ((none : Option (List A)).getD []) = ([] : List A) from rfl,
    ← markedSquare_eq_msBlocks]
  rw [show markedSquare A b₀ :: bs.map (markedSquare A)
    = (splitSep v).map (markedSquare A) by rw [hv]; rfl]
  simp [mapLift, blockStr, List.map_map, Function.comp_def]

/-! ## The map lifting of a polyregular function -/

/-- **The map lifting of a polyregular function is polyregular**, in the form in which the
induction on the composition of primes is carried out. -/
theorem isPolyregular_mapLift_aux {A B : Type} {f : List A → List B}
    (hf : IsPolyregular f) : Finite A → Finite B → IsPolyregular (mapLift f) := by
  induction hf with
  | @base A B f h =>
      intro hA hB
      haveI := hA; haveI := hB
      rcases h with hreg | ⟨A₀, e, e', hfe⟩
      · exact IsPolyregular.of_regular (isRegularFun_mapLift hreg)
      · haveI : Finite A₀ := Finite.of_equiv A e
        haveI : Finite (A₀ ⊕ A₀) := inferInstance
        have hcomp : f = (fun u : List (A₀ ⊕ A₀) => u.map e'.symm) ∘
            (markedSquare A₀) ∘ (fun w : List A => w.map e) := by
          funext w; exact hfe w
        have h1 : IsPolyregular (fun v : List (Option A) => v.map (Option.map e)) :=
          IsPolyregular.of_regular (IsRegularFun.of_rational
            (isRationalFun_map (Option.map (e : A → A₀))))
        have h2 : IsPolyregular (mapLift (markedSquare A₀)) :=
          isPolyregular_mapLift_markedSquare A₀
        have h3 : IsPolyregular (fun v : List (Option (A₀ ⊕ A₀)) =>
            v.map (Option.map (e'.symm : A₀ ⊕ A₀ → B))) :=
          IsPolyregular.of_regular (IsRegularFun.of_rational
            (isRationalFun_map (Option.map (e'.symm : A₀ ⊕ A₀ → B))))
        refine ((h1.comp' h2 (fun _ => rfl)).comp' h3 (fun _ => rfl)).congr (fun v => ?_)
        show (mapLift (markedSquare A₀) (v.map (Option.map e))).map (Option.map e'.symm)
          = mapLift f v
        rw [hcomp]
        rw [show ((fun u : List (A₀ ⊕ A₀) => u.map e'.symm) ∘
            (markedSquare A₀) ∘ (fun w : List A => w.map e))
          = ((fun u : List (A₀ ⊕ A₀) => u.map e'.symm) ∘
            ((markedSquare A₀) ∘ (fun w : List A => w.map e))) from rfl]
        rw [mapLift_comp', mapLift_comp']
        show _ = mapLift (fun u : List (A₀ ⊕ A₀) => u.map e'.symm)
          (mapLift (markedSquare A₀) (mapLift (fun w : List A => w.map e) v))
        rw [mapLift_letterMap, mapLift_letterMap]
  | id A =>
      intro _ _
      rw [mapLift_id]
      exact isPolyregular_id
  | @comp A B C hB f g _ _ ihf ihg =>
      intro hA hC
      haveI := hA; haveI := hB; haveI := hC
      rw [mapLift_comp']
      exact (ihf hA hB).comp (ihg hB hC)

/-- **The map lifting of a polyregular function is polyregular.** -/
theorem isPolyregular_mapLift {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPolyregular f) : IsPolyregular (mapLift f) :=
  isPolyregular_mapLift_aux hf ‹_› ‹_›

end Transducers
