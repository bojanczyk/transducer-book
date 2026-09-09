/-
Part D: processing every split of the input, and the polyregularity of such a computation.

This file provides the one construction that all the polyregular functions of Section *A functional
programming language* of *Transducers* (M. Bojańczyk) are built from.  Write

    prefCopy w i = a₁ ⋯ aᵢ  aᵢ₊₁ ⋯ aₙ         (the first `i` letters underlined)

for the input `w = a₁ ⋯ aₙ` with a prefix underlined -- underlining is `Sum.inl` and no underlining
is `Sum.inr` -- and let

    perSplit h w = h (prefCopy w 0) ⋯ h (prefCopy w n)

be the concatenation of the results of applying a function `h` to all `n+1` of these copies.  The
theorem of this file, `Transducers.isPolyregular_perSplit`, is that `perSplit h` is polyregular
whenever `h` is regular and maps the empty string to the empty string.

The proof is the one sentence of the book's proof of Theorem `thm:polyregular-terms`, made
explicit.  Marked squaring (Example 33, `Transducers.markedSquare`) is polyregular by definition,
and the marked square of the input with a fresh marker `#` in front,

    # a₁ ⋯ aₙ,

is the concatenation of the `n+1` copies of `# a₁ ⋯ aₙ` in which a prefix ending at the marker or
at one of the letters is underlined; the marker is underlined in every copy, and it is the *only*
letter that can be the last underlined one in the copy where the prefix is just the marker.  So a
letter-to-letter map that sends the underlined marker to the separator `#` and forgets nothing else
turns the marked square into

    # (prefCopy w 0) # (prefCopy w 1) ⋯ # (prefCopy w n),

which is a string whose blocks -- in the sense of the map lifting `Transducers.mapLift` of Part A --
are exactly the copies, preceded by one empty block.  The map lifting of `h` then applies `h` to
every copy, and a homomorphism erases the separators.  Both of these are regular, so the whole
composition is polyregular.

The requirement `h [] = []` is what makes the leading empty block harmless.
-/
import RequestProject.PartD.PolyDef

namespace Transducers

variable {X Y Z : Type}

/-! ## The copies of an input -/

/-- The input `w` with its first `i` letters underlined: underlining is `Sum.inl`. -/
def prefCopy (w : List X) (i : ℕ) : List (X ⊕ X) :=
  (w.take i).map Sum.inl ++ (w.drop i).map Sum.inr

/-- All the ways of underlining a prefix of `w`, from the empty prefix to the whole of `w`. -/
def prefCopies (w : List X) : List (List (X ⊕ X)) :=
  (List.range (w.length + 1)).map (prefCopy w)

/-- Apply `h` to every copy of the input and concatenate the results. -/
def perSplit (h : List (X ⊕ X) → List Y) (w : List X) : List Y :=
  ((prefCopies w).map h).flatten

@[simp] lemma prefCopy_zero (w : List X) : prefCopy w 0 = w.map Sum.inr := by
  simp [prefCopy]

lemma prefCopy_succ (x : X) (w : List X) (i : ℕ) :
    prefCopy (x :: w) (i + 1) = Sum.inl x :: prefCopy w i := by
  simp [prefCopy]

lemma prefCopy_length (w : List X) : prefCopy w w.length = w.map Sum.inl := by
  simp [prefCopy]

@[simp] lemma prefCopies_nil : prefCopies ([] : List X) = [[]] := by
  simp [prefCopies, prefCopy]

lemma prefCopies_cons (x : X) (w : List X) :
    prefCopies (x :: w)
      = ((x :: w).map Sum.inr) :: (prefCopies w).map (fun c => Sum.inl x :: c) := by
  unfold prefCopies
  rw [show (x :: w).length + 1 = (w.length + 1) + 1 from rfl, List.range_succ_eq_map]
  simp [prefCopy_succ, List.map_map, Function.comp_def]

@[simp] lemma perSplit_nil (h : List (X ⊕ X) → List Y) : perSplit h ([] : List X) = h [] := by
  simp [perSplit]

lemma perSplit_cons (h : List (X ⊕ X) → List Y) (x : X) (w : List X) :
    perSplit h (x :: w)
      = h ((x :: w).map Sum.inr) ++ ((prefCopies w).map (fun c => h (Sum.inl x :: c))).flatten := by
  simp [perSplit, prefCopies_cons, List.map_map, Function.comp_def]

/-! ## Running over the copies from left to right -/

/-- The copies of `w`, with a fixed underlined prefix `P` in front of every one of them.  This is
what `Transducers.perSplit` looks like once the first letters of the input have been consumed, and
it is how the computations over the copies are carried out by induction. -/
def perSplitFrom (h : List (X ⊕ X) → List Y) (P w : List X) : List Y :=
  ((prefCopies w).map (fun c => h (P.map Sum.inl ++ c))).flatten

lemma perSplitFrom_nil (h : List (X ⊕ X) → List Y) (P : List X) :
    perSplitFrom h P [] = h (P.map Sum.inl) := by
  simp [perSplitFrom]

lemma perSplitFrom_cons (h : List (X ⊕ X) → List Y) (P : List X) (x : X) (w : List X) :
    perSplitFrom h P (x :: w)
      = h (P.map Sum.inl ++ (x :: w).map Sum.inr) ++ perSplitFrom h (P ++ [x]) w := by
  unfold perSplitFrom
  rw [prefCopies_cons, List.map_cons, List.flatten_cons, List.map_map]
  congr 1
  congr 1
  refine List.map_congr_left (fun c _ => ?_)
  show h (P.map Sum.inl ++ (Sum.inl x :: c)) = h ((P ++ [x]).map Sum.inl ++ c)
  congr 1
  simp

lemma perSplit_eq_perSplitFrom (h : List (X ⊕ X) → List Y) (w : List X) :
    perSplit h w = perSplitFrom h [] w := by
  simp [perSplit, perSplitFrom]

/-! ## Strings presented as lists of blocks -/

/-- The string over `X + 1` whose blocks, in the sense of the map lifting `Transducers.mapLift`,
are the given ones. -/
def blockStr (bs : List (List X)) : List (Option X) :=
  List.intercalate [none] (bs.map (fun b => b.map some))

lemma splitSep_blockStr : ∀ (bs : List (List X)), bs ≠ [] → splitSep (blockStr bs) = bs := by
  intro bs
  induction bs with
  | nil => intro h; exact absurd rfl h
  | cons b bs ih =>
      intro _
      by_cases hbs : bs = []
      · subst hbs
        have h0 := splitSep_map_some_append b ([] : List (Option X)) [] [] rfl
        simpa [blockStr, List.intercalate] using h0
      · rw [blockStr, List.map_cons,
          intercalate_cons_cons _ _ _ (by simpa using hbs)]
        rw [show (b.map (some : X → Option X)) ++ [none] ++
            List.intercalate [none] (bs.map (fun c => c.map (some : X → Option X)))
          = b.map some ++ ((none : Option X) ::
            List.intercalate [none] (bs.map (fun c => c.map (some : X → Option X)))) by simp]
        rw [splitSep_map_some_append b _ [] bs (by
          show splitSep ((none : Option X) :: blockStr bs) = [] :: bs
          rw [show splitSep ((none : Option X) :: blockStr bs) = [] :: splitSep (blockStr bs)
            from rfl, ih hbs])]
        simp

@[simp] lemma blockStr_singleton (b : List X) : blockStr [b] = b.map some := by
  simp [blockStr, List.intercalate]

lemma blockStr_cons (b : List X) (bs : List (List X)) (h : bs ≠ []) :
    blockStr (b :: bs) = b.map some ++ ((none : Option X) :: blockStr bs) := by
  rw [blockStr, List.map_cons, intercalate_cons_cons _ _ _ (by simpa using h)]
  simp [blockStr]

lemma blockStr_cons_append (y z : List X) (bs : List (List X)) :
    blockStr ((y ++ z) :: bs) = y.map some ++ blockStr (z :: bs) := by
  cases bs with
  | nil => simp
  | cons c cs =>
      rw [blockStr_cons (y ++ z) (c :: cs) (by simp), blockStr_cons z (c :: cs) (by simp)]
      simp

lemma mapLift_blockStr (f : List X → List Y) (bs : List (List X)) (h : bs ≠ []) :
    mapLift f (blockStr bs) = blockStr (bs.map f) := by
  rw [mapLift, splitSep_blockStr bs h, blockStr, List.map_map]
  rfl

lemma homOf_blockStr {Y : Type} (sig : Option X → List Y) (hsig : sig none = [])
    (bs : List (List X)) :
    homOf sig (blockStr bs) = (bs.map (fun b => homOf sig (b.map some))).flatten := by
  induction bs with
  | nil => simp [blockStr, homOf, List.intercalate]
  | cons b bs ih =>
      by_cases hbs : bs = []
      · subst hbs; simp [blockStr, List.intercalate]
      · rw [blockStr, List.map_cons, intercalate_cons_cons _ _ _ (by simpa using hbs)]
        rw [show (b.map (some : X → Option X)) ++ [none] ++
            List.intercalate [none] (bs.map (fun c => c.map (some : X → Option X)))
          = b.map some ++ ([none] ++ blockStr bs) by simp [blockStr]]
        simp only [homOf, List.map_append, List.flatten_append] at ih ⊢
        rw [show ([(none : Option X)].map sig).flatten = [] by simp [hsig]]
        simpa using ih

/-! ## Two regular languages used by the functions on the copies -/

lemma foldl_or_any {Γ : Type} (p : Γ → Bool) :
    ∀ (u : List Γ) (b : Bool), u.foldl (fun b x => b || p x) b = (b || u.any p) := by
  intro u
  induction u with
  | nil => intro b; simp
  | cons x u ih => intro b; simp [ih, Bool.or_assoc]

/-- The language of the strings that have a letter satisfying `p` is regular. -/
lemma isRegular_anyLang {Γ : Type} (p : Γ → Bool) :
    Language.IsRegular {u : List Γ | u.any p = true} := by
  refine RegAut.isRegular_of_eq
    (RegAut.isRegular_foldl (Γ := Γ) (fun b x => b || p x) false ({true} : Set Bool))
    (fun u => ?_)
  show u.any p = true ↔ (u.foldl (fun b x => b || p x) false ∈ ({true} : Set Bool))
  rw [foldl_or_any]
  simp

/-! ## The auxiliary maps of the construction -/

namespace PerSplit

/-- The letter-to-letter map that turns the marked square of `# w` into the copies of `w`,
separated by the marker: the underlined marker becomes the separator, and every other letter keeps
its underlining. -/
def phi : (Option X ⊕ Option X) → Option (X ⊕ X)
  | Sum.inl (some x) => some (Sum.inl x)
  | Sum.inr (some x) => some (Sum.inr x)
  | _ => none

/-- The marked square of `# w`, read through `phi`, is the list of the copies of `w`, each preceded
by the separator. -/
lemma map_phi_markedSquare (w : List X) :
    (markedSquare (Option X) (none :: w.map some)).map phi
      = ((prefCopies w).map (fun c => none :: c.map some)).flatten := by
  set v : List (Option X) := none :: w.map some with hv
  have hlen : v.length = w.length + 1 := by simp [hv]
  rw [markedSquare, List.map_flatten, List.map_map, hlen]
  unfold prefCopies
  rw [List.map_map]
  congr 1
  refine List.map_congr_left (fun i _ => ?_)
  have htake : v.take (i + 1) = none :: (w.take i).map some := by
    rw [hv, List.take_succ_cons, List.map_take]
  have hdrop : v.drop (i + 1) = (w.drop i).map some := by
    rw [hv, List.drop_succ_cons, List.map_drop]
  show (((v.take (i + 1)).map Sum.inl ++ (v.drop (i + 1)).map Sum.inr).map phi) = _
  rw [htake, hdrop]
  simp [prefCopy, List.map_map, Function.comp_def, phi]

/-- The blocks of the concatenation of the copies, each preceded by the separator, are the copies,
preceded by one empty block. -/
lemma splitSep_blocks (bs : List (List Z)) :
    splitSep ((bs.map (fun b => (none : Option Z) :: b.map some)).flatten) = [] :: bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rw [List.map_cons, List.flatten_cons, List.cons_append,
        show splitSep ((none : Option Z) :: (b.map some ++
          (bs.map (fun b => (none : Option Z) :: b.map some)).flatten))
          = [] :: splitSep (b.map some ++
              (bs.map (fun b => (none : Option Z) :: b.map some)).flatten) from rfl]
      cases hb : splitSep ((bs.map (fun b => (none : Option Z) :: b.map some)).flatten) with
      | nil => exact absurd hb (splitSep_ne_nil _)
      | cons c cs =>
          rw [splitSep_map_some_append b _ c cs hb]
          rw [hb] at ih
          have h1 : c = [] := (List.cons.inj ih).1
          have h2 : cs = bs := (List.cons.inj ih).2
          rw [h1, h2]
          simp

/-- Erasing the separators of a map lifting concatenates the results of the lifted function on the
blocks. -/
lemma del_mapLift (h : List Z → List Y) (u : List (Option Z)) :
    RegCl.del (mapLift h u) = ((splitSep u).map h).flatten := by
  have hdel_some : ∀ y : List Y, RegCl.del (y.map (some : Y → Option Y)) = y := by
    intro y
    induction y with
    | nil => rfl
    | cons a y ih => simpa [RegCl.del, homOf] using ih
  have key : ∀ ys : List (List Y),
      RegCl.del (List.intercalate [none] (ys.map (fun l => l.map some))) = ys.flatten := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih =>
        by_cases hys : ys = []
        · subst hys
          rw [show ([y].map (fun l : List Y => l.map some))
            = [y.map (some : Y → Option Y)] from rfl]
          rw [show List.intercalate [(none : Option Y)] [y.map (some : Y → Option Y)]
            = y.map some by simp [List.intercalate]]
          rw [hdel_some]
          simp
        · rw [List.map_cons, intercalate_cons_cons _ _ _ (by simpa using hys)]
          rw [show (y.map some) ++ [none] ++
              List.intercalate [none] (ys.map (fun l : List Y => l.map some))
            = (y.map some) ++ ((none : Option Y) ::
              List.intercalate [none] (ys.map (fun l : List Y => l.map some))) by simp]
          rw [show RegCl.del ((y.map some) ++ ((none : Option Y) ::
              List.intercalate [none] (ys.map (fun l : List Y => l.map some))))
            = RegCl.del (y.map some) ++ RegCl.del ((none : Option Y) ::
              List.intercalate [none] (ys.map (fun l : List Y => l.map some))) by
            simp [RegCl.del, homOf]]
          have h1 : RegCl.del (y.map (some : Y → Option Y)) = y := hdel_some y
          have h2 : RegCl.del ((none : Option Y) ::
              List.intercalate [none] (ys.map (fun l : List Y => l.map some)))
            = RegCl.del (List.intercalate [none] (ys.map (fun l : List Y => l.map some))) := by
            simp [RegCl.del, homOf]
          rw [h1, h2, ih]
          simp
  rw [mapLift, show ((splitSep u).map (fun v => (h v).map some))
      = (((splitSep u).map h).map (fun l => l.map some)) by
    simp [List.map_map, Function.comp_def], key]

end PerSplit

/-! ## The polyregularity of `perSplit` -/

open PerSplit in
/-- **Applying a regular function to every copy of the input is polyregular.**  This is the
construction that the book's proof of Theorem `thm:polyregular-terms` uses for the new atomic
function: an outermost loop marks the position at which the input is cut, and the rest of the
computation is regular. -/
theorem isPolyregular_perSplit [Finite X] [Finite Y] {h : List (X ⊕ X) → List Y}
    (hh : IsRegularFun h) (h0 : h [] = []) : IsPolyregular (perSplit h) := by
  haveI : Finite (X ⊕ X) := inferInstance
  have hmark : IsPolyregular (fun w : List X => none :: w.map some) :=
    IsPolyregular.of_regular (IsRegularFun.of_rational
      (isRationalFun_comp (isRationalFun_map (some : X → Option X))
        (isRationalFun_cons (none : Option X))))
  have hms : IsPolyregular (markedSquare (Option X)) := isPolyregular_markedSquare (Option X)
  have hphi : IsPolyregular (fun u : List (Option X ⊕ Option X) => u.map phi) :=
    IsPolyregular.of_regular (IsRegularFun.of_rational (isRationalFun_map phi))
  have hml : IsPolyregular (mapLift h) := IsPolyregular.of_regular (isRegularFun_mapLift hh)
  have hdel : IsPolyregular (RegCl.del : List (Option Y) → List Y) :=
    IsPolyregular.of_regular RegCl.isRegularFun_del
  have hcomp := ((((hmark.comp' hms (fun _ => rfl)).comp' hphi (fun _ => rfl)).comp'
    hml (fun _ => rfl)).comp' hdel (fun _ => rfl))
  refine hcomp.congr (fun w => ?_)
  show RegCl.del (mapLift h ((markedSquare (Option X) (none :: w.map some)).map phi))
    = perSplit h w
  rw [map_phi_markedSquare, del_mapLift, splitSep_blocks]
  simp [perSplit, h0]

end Transducers
