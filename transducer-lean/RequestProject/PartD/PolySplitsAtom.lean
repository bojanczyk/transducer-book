/-
Part D: the new atomic function of Definition `def:polyregular-terms` is polyregular under string
representation.

The function is `Transducers.splitsList`,

    [a₁,…,aₙ] ↦ [([a₁,…,aₙ],[]), ([a₁,…,a_{n-1}],[aₙ]), …, ([],[a₁,…,aₙ])],

and what has to be produced from the string `[r₁,…,rₙ]` -- the representation of the input, whose
entries `rᵢ` are the representations of the `aᵢ` -- is the string

    [([],[r₁,…,rₙ]),([r₁],[r₂,…,rₙ]),…,([r₁,…,rₙ],[])]

read backwards, that is, with the pairs in the order of *decreasing* prefix.  The order is repaired
at the end by the reverse of Definition `def:regular-terms`, which is regular, so the work is to
produce the pairs in the order of increasing prefix.  That is exactly a computation over all the
ways of cutting the input into a prefix and a suffix
(`Transducers.perSplit`, `RequestProject/PartD/PolyPerSplit.lean`), and the whole construction is:

* mark the top-level commas of the representation, which is the machine of
  `RequestProject/PartC/CombMark.lean`: the string becomes `r₁ # r₂ # ⋯ # rₙ`;
* append `# $`, so that the string is `r₁ # r₂ # ⋯ # rₙ # $`;  the extra separator is the one that
  marks the cut that takes the whole list as its prefix, and the sentinel `$` closes the string;
* run over all the cuts of that string.  A cut is *relevant* when it is at the very beginning of
  the string (the empty prefix) or just before a separator `#` (the prefix is a whole number of
  entries), and all the other cuts contribute nothing.  This is a regular property of the copy:
  the letters before the cut are underlined and the letters after it are not, so it says that the
  first letter that is not underlined is a separator, or that no letter is underlined at all;
* on a relevant copy, a sequential rewriting produces `,([r₁,…,r_j],[r_{j+1},…,rₙ])`: the
  underlined separators become commas, the first letter that is not underlined produces `],[`, the
  later separators become commas again -- with the last one, which is the separator that was
  appended, producing nothing, which is what the two right-hand states of the rewriting are for --
  and the sentinel produces nothing;
* the leading comma of the whole string is removed and the outer brackets are added.
-/
import RequestProject.PartD.PolyRepr
import RequestProject.PartD.PolyTerms
import RequestProject.PartC.RegAut
import RequestProject.PartC.RatSeq

namespace Transducers

open Comb

namespace SplitsAtom

/-- The alphabet of the string that the construction runs over: `none` is the sentinel `$`,
`some none` is the separator `#`, and `some (some c)` is a letter of the representation. -/
abbrev Gam : Type := Option (Option Sym8)

/-- The sentinel. -/
abbrev dollar : Gam := none

/-- The separator. -/
abbrev hash : Gam := some none

/-- A letter of the representation. -/
abbrev lett (c : Sym8) : Gam := some (some c)

/-! ## The test that selects the relevant cuts -/

/-- The states of the automaton that recognises the relevant copies. -/
inductive SelSt | start | left | acc | rej
  deriving DecidableEq, Fintype

/-- Its transition function: a copy is relevant if its first letter is not underlined, or if the
first letter that is not underlined is a separator. -/
def selStep : SelSt → (Gam ⊕ Gam) → SelSt
  | SelSt.start, Sum.inl _ => SelSt.left
  | SelSt.start, Sum.inr _ => SelSt.acc
  | SelSt.left, Sum.inl _ => SelSt.left
  | SelSt.left, Sum.inr (some none) => SelSt.acc
  | SelSt.left, Sum.inr _ => SelSt.rej
  | SelSt.acc, _ => SelSt.acc
  | SelSt.rej, _ => SelSt.rej

/-- The language of the relevant copies. -/
def selLang : Language (Gam ⊕ Gam) :=
  {c : List (Gam ⊕ Gam) | c.foldl selStep SelSt.start ∈ ({SelSt.acc} : Set SelSt)}

lemma selLang_isRegular : selLang.IsRegular := RegAut.isRegular_foldl selStep SelSt.start _

/-! ## The sequential rewriting that produces one pair -/

/-- The states of the sequential rewriting: reading the underlined prefix; reading the suffix,
with no separator pending; reading the suffix, with a separator pending. -/
inductive SplitMode | left | rightFresh | rightPending
  deriving DecidableEq, Fintype

/-- Its transition function. -/
def splitStep : SplitMode → (Gam ⊕ Gam) → SplitMode
  | SplitMode.left, Sum.inl _ => SplitMode.left
  | SplitMode.left, Sum.inr _ => SplitMode.rightFresh
  | SplitMode.rightFresh, Sum.inr (some none) => SplitMode.rightPending
  | SplitMode.rightFresh, _ => SplitMode.rightFresh
  | SplitMode.rightPending, Sum.inr (some (some _)) => SplitMode.rightFresh
  | SplitMode.rightPending, _ => SplitMode.rightPending

/-- Its output function.  In the underlined prefix, a separator is a comma and a letter is itself;
the first letter that is not underlined opens the second component of the pair with `],[`; in the
suffix, a separator is remembered and turned into a comma when the next letter arrives, so that the
separator that was appended at the end produces nothing; the sentinel produces nothing. -/
def splitOut : SplitMode → (Gam ⊕ Gam) → List Sym8
  | SplitMode.left, Sum.inl (some none) => [Sym8.comma]
  | SplitMode.left, Sum.inl (some (some c)) => [c]
  | SplitMode.left, Sum.inl none => []
  | SplitMode.left, Sum.inr (some (some c)) => [Sym8.rbrack, Sym8.comma, Sym8.lbrack, c]
  | SplitMode.left, Sum.inr _ => [Sym8.rbrack, Sym8.comma, Sym8.lbrack]
  | SplitMode.rightFresh, Sum.inr (some (some c)) => [c]
  | SplitMode.rightFresh, _ => []
  | SplitMode.rightPending, Sum.inr (some (some c)) => [Sym8.comma, c]
  | SplitMode.rightPending, _ => []

/-- Its final output: the pair is closed. -/
def splitFin : SplitMode → List Sym8 := fun _ => [Sym8.rbrack, Sym8.rpar]

open Classical in
/-- The function that is applied to every copy: nothing on the copies that do not describe a cut
between two entries, and the pair of the prefix and the suffix, preceded by a comma, on those that
do. -/
noncomputable def onCopy (c : List (Gam ⊕ Gam)) : List Sym8 :=
  if c ∈ selLang then
    [Sym8.comma, Sym8.lpar, Sym8.lbrack] ++ seqFinEval splitStep splitOut splitFin SplitMode.left c
  else []

lemma onCopy_nil : onCopy ([] : List (Gam ⊕ Gam)) = [] := by
  classical
  have : ([] : List (Gam ⊕ Gam)) ∉ selLang := by
    show ¬ (([] : List (Gam ⊕ Gam)).foldl selStep SelSt.start ∈ ({SelSt.acc} : Set SelSt))
    simp
  rw [onCopy, if_neg this]

lemma isRegularFun_onCopy : IsRegularFun onCopy := by
  classical
  refine isRegularFun_cond ?_
    (IsRegularFun.of_rational (isRationalFun_const [])) selLang_isRegular
  exact isRegularFun_concat
    (IsRegularFun.of_rational (isRationalFun_const [Sym8.comma, Sym8.lpar, Sym8.lbrack]))
    (IsRegularFun.of_rational
      (isRationalFun_seqFinEval splitStep SplitMode.left splitOut splitFin))

/-! ## The strings that the construction runs over, and what it produces on them -/

/-- The string `r₁ # r₂ # ⋯ # rₖ #`: the blocks, each followed by a separator. -/
def flatStr (cs : List (List Sym8)) : List Gam :=
  (cs.map (fun r => r.map lett ++ [hash])).flatten

@[simp] lemma flatStr_nil : flatStr [] = [] := rfl

lemma flatStr_cons (r : List Sym8) (cs : List (List Sym8)) :
    flatStr (r :: cs) = r.map lett ++ ([hash] ++ flatStr cs) := by
  simp [flatStr]

/-- The strings of a list of blocks, each preceded by a comma. -/
def commaJoin (cs : List (List Sym8)) : List Sym8 :=
  (cs.map (fun x => Sym8.comma :: x)).flatten

lemma joinSep_cons_commaJoin (y : List Sym8) :
    ∀ xs : List (List Sym8), joinSep (y :: xs) = y ++ commaJoin xs := by
  intro xs
  induction xs generalizing y with
  | nil => simp [commaJoin]
  | cons z zs ih =>
      rw [joinSep_cons_cons, ih z]
      simp [commaJoin]

lemma tail_commaJoin (xs : List (List Sym8)) : (commaJoin xs).tail = joinSep xs := by
  cases xs with
  | nil => rfl
  | cons y ys =>
      rw [commaJoin, List.map_cons, List.flatten_cons, List.cons_append, List.tail_cons,
        joinSep_cons_commaJoin]
      rfl

/-- The marked representation of a nonempty list of blocks, followed by the separator that the
construction appends, is the string of the blocks. -/
lemma optBlocks_map_some_append (bs : List (List Sym8)) (hbs : bs ≠ []) :
    (Comb.optBlocks bs).map (some : Option Sym8 → Gam) ++ [hash] = flatStr bs := by
  induction bs with
  | nil => exact absurd rfl hbs
  | cons r bs ih =>
      cases bs with
      | nil => simp [flatStr, Comb.optBlocks, List.map_map, Function.comp_def]
      | cons r' bs' =>
          rw [Comb.optBlocks_cons, Comb.optBlocksTail_cons, flatStr_cons, ← ih (by simp)]
          simp [List.map_map, Function.comp_def]

/-! ## The sequential rewriting on the part of the copy that is not underlined -/

/-- The sequential rewriting of `Transducers.SplitsAtom.splitOut`, run from a given mode on a part
of the copy that is not underlined. -/
def runFrom (m : SplitMode) (S : List Gam) : List Sym8 :=
  seqFinEval splitStep splitOut splitFin m (S.map Sum.inr)

@[simp] lemma runFrom_nil (m : SplitMode) : runFrom m [] = [Sym8.rbrack, Sym8.rpar] := rfl

lemma runFrom_cons (m : SplitMode) (x : Gam) (S : List Gam) :
    runFrom m (x :: S) = splitOut m (Sum.inr x) ++ runFrom (splitStep m (Sum.inr x)) S := rfl

/-- What the underlined prefix of a copy contributes: the separators become commas. -/
def leftOut (P : List Gam) : List Sym8 :=
  (P.map (fun x => splitOut SplitMode.left (Sum.inl x))).flatten

@[simp] lemma leftOut_nil : leftOut [] = [] := rfl

lemma leftOut_append (P Q : List Gam) : leftOut (P ++ Q) = leftOut P ++ leftOut Q := by
  simp [leftOut]

lemma leftOut_letters (r : List Sym8) : leftOut (r.map lett) = r := by
  induction r with
  | nil => rfl
  | cons c r ih => simpa [leftOut, lett, splitOut] using ih

@[simp] lemma leftOut_hash : leftOut [hash] = [Sym8.comma] := rfl

lemma seqFinEval_inl_append (P : List Gam) (Z : List (Gam ⊕ Gam)) :
    seqFinEval splitStep splitOut splitFin SplitMode.left (P.map Sum.inl ++ Z)
      = leftOut P ++ seqFinEval splitStep splitOut splitFin SplitMode.left Z := by
  induction P with
  | nil => simp
  | cons x P ih =>
      rw [List.map_cons, List.cons_append, seqFinEval_cons,
        show splitStep SplitMode.left (Sum.inl x) = SplitMode.left from rfl, ih]
      simp [leftOut]

/-- On the part of the copy that is not underlined, the rewriting produces the second component of
the pair: after a separator, the entries that follow, each preceded by a comma. -/
lemma runFrom_flat :
    ∀ cs : List (List Sym8), (∀ x ∈ cs, x ≠ []) →
      runFrom SplitMode.rightPending (flatStr cs ++ [dollar]) = commaJoin cs ++ [Sym8.rbrack, Sym8.rpar]
      ∧ ∀ r : List Sym8, runFrom SplitMode.rightFresh (r.map lett ++ ([hash] ++ flatStr cs ++ [dollar]))
          = r ++ commaJoin cs ++ [Sym8.rbrack, Sym8.rpar] := by
  intro cs
  induction cs with
  | nil =>
      intro _
      constructor
      · simp [flatStr, runFrom_cons, splitOut, splitStep, commaJoin, dollar]
      · intro r
        induction r with
        | nil => simp [flatStr, runFrom_cons, splitOut, splitStep, commaJoin, dollar, hash]
        | cons c r ih => simpa [runFrom_cons, splitOut, splitStep, lett] using ih
  | cons r₀ cs ih =>
      intro hcs
      have hr₀ : r₀ ≠ [] := hcs r₀ (by simp)
      have hcs' : ∀ x ∈ cs, x ≠ [] := fun x hx => hcs x (by simp [hx])
      obtain ⟨c, r₀', rfl⟩ : ∃ c r', r₀ = c :: r' := by
        cases r₀ with
        | nil => exact absurd rfl hr₀
        | cons c r' => exact ⟨c, r', rfl⟩
      have hpend : runFrom SplitMode.rightPending (flatStr ((c :: r₀') :: cs) ++ [dollar])
          = commaJoin ((c :: r₀') :: cs) ++ [Sym8.rbrack, Sym8.rpar] := by
        rw [flatStr_cons]
        rw [show ((c :: r₀').map lett ++ ([hash] ++ flatStr cs)) ++ [dollar]
          = lett c :: (r₀'.map lett ++ ([hash] ++ flatStr cs ++ [dollar])) by simp]
        rw [runFrom_cons,
          show splitOut SplitMode.rightPending (Sum.inr (lett c)) = [Sym8.comma, c] from rfl,
          show splitStep SplitMode.rightPending (Sum.inr (lett c)) = SplitMode.rightFresh from rfl,
          (ih hcs').2 r₀']
        simp [commaJoin]
      refine ⟨hpend, fun r => ?_⟩
      induction r with
      | nil =>
          rw [List.map_nil, List.nil_append,
            show ([hash] ++ flatStr ((c :: r₀') :: cs) ++ [dollar])
              = hash :: (flatStr ((c :: r₀') :: cs) ++ [dollar]) by simp]
          rw [runFrom_cons,
            show splitOut SplitMode.rightFresh (Sum.inr hash) = [] from rfl,
            show splitStep SplitMode.rightFresh (Sum.inr hash) = SplitMode.rightPending from rfl,
            hpend]
          simp
      | cons c' r ih' => simpa [runFrom_cons, splitOut, splitStep, lett] using ih'

lemma runFrom_fresh_flat (cs : List (List Sym8)) (hcs : ∀ x ∈ cs, x ≠ []) :
    runFrom SplitMode.rightFresh (flatStr cs ++ [dollar])
      = joinSep cs ++ [Sym8.rbrack, Sym8.rpar] := by
  cases cs with
  | nil => simp [flatStr, runFrom_cons, splitOut, splitStep, dollar]
  | cons r cs =>
      have hr : r ≠ [] := hcs r (by simp)
      have hcs' : ∀ x ∈ cs, x ≠ [] := fun x hx => hcs x (by simp [hx])
      obtain ⟨c, r', rfl⟩ : ∃ c r', r = c :: r' := by
        cases r with
        | nil => exact absurd rfl hr
        | cons c r' => exact ⟨c, r', rfl⟩
      rw [flatStr_cons,
        show ((c :: r').map lett ++ ([hash] ++ flatStr cs)) ++ [dollar]
          = (c :: r').map lett ++ ([hash] ++ flatStr cs ++ [dollar]) by simp,
        (runFrom_flat cs hcs').2 (c :: r'), joinSep_cons_commaJoin]

lemma runFrom_left_hash (cs : List (List Sym8)) (hcs : ∀ x ∈ cs, x ≠ []) :
    runFrom SplitMode.left (hash :: (flatStr cs ++ [dollar]))
      = [Sym8.rbrack, Sym8.comma, Sym8.lbrack] ++ (joinSep cs ++ [Sym8.rbrack, Sym8.rpar]) := by
  rw [runFrom_cons,
    show splitOut SplitMode.left (Sum.inr hash) = [Sym8.rbrack, Sym8.comma, Sym8.lbrack] from rfl,
    show splitStep SplitMode.left (Sum.inr hash) = SplitMode.rightFresh from rfl,
    runFrom_fresh_flat cs hcs]

lemma runFrom_left_flat (cs : List (List Sym8)) (hcs : ∀ x ∈ cs, x ≠ []) (hne : cs ≠ []) :
    runFrom SplitMode.left (flatStr cs ++ [dollar])
      = [Sym8.rbrack, Sym8.comma, Sym8.lbrack] ++ (joinSep cs ++ [Sym8.rbrack, Sym8.rpar]) := by
  cases cs with
  | nil => exact absurd rfl hne
  | cons r cs =>
      have hr : r ≠ [] := hcs r (by simp)
      have hcs' : ∀ x ∈ cs, x ≠ [] := fun x hx => hcs x (by simp [hx])
      obtain ⟨c, r', rfl⟩ : ∃ c r', r = c :: r' := by
        cases r with
        | nil => exact absurd rfl hr
        | cons c r' => exact ⟨c, r', rfl⟩
      rw [flatStr_cons,
        show ((c :: r').map lett ++ ([hash] ++ flatStr cs)) ++ [dollar]
          = lett c :: (r'.map lett ++ ([hash] ++ flatStr cs ++ [dollar])) by simp]
      rw [runFrom_cons,
        show splitOut SplitMode.left (Sum.inr (lett c))
          = [Sym8.rbrack, Sym8.comma, Sym8.lbrack, c] from rfl,
        show splitStep SplitMode.left (Sum.inr (lett c)) = SplitMode.rightFresh from rfl,
        (runFrom_flat cs hcs').2 r', joinSep_cons_commaJoin]
      simp

/-! ## The value of the function on a copy -/

lemma foldl_sel_inl :
    ∀ P : List Gam,
      (P.map Sum.inl).foldl selStep SelSt.start = if P = [] then SelSt.start else SelSt.left := by
  intro P
  have key : ∀ (P : List Gam), (P.map Sum.inl).foldl selStep SelSt.left = SelSt.left := by
    intro P
    induction P with
    | nil => rfl
    | cons x P ih => simpa [selStep] using ih
  cases P with
  | nil => rfl
  | cons x P => simpa [selStep] using key P

lemma foldl_sel_acc (S : List Gam) : (S.map Sum.inr).foldl selStep SelSt.acc = SelSt.acc := by
  induction S with
  | nil => rfl
  | cons x S ih => simpa [selStep] using ih

lemma foldl_sel_rej (S : List Gam) : (S.map Sum.inr).foldl selStep SelSt.rej = SelSt.rej := by
  induction S with
  | nil => rfl
  | cons x S ih => simpa [selStep] using ih

lemma onCopy_hash (P : List Gam) (hP : P ≠ []) (Z : List Gam) :
    onCopy (P.map Sum.inl ++ (hash :: Z).map Sum.inr)
      = [Sym8.comma, Sym8.lpar, Sym8.lbrack] ++ (leftOut P ++ runFrom SplitMode.left (hash :: Z)) := by
  classical
  have hmem : (P.map Sum.inl ++ (hash :: Z).map Sum.inr) ∈ selLang := by
    show (P.map Sum.inl ++ (hash :: Z).map Sum.inr).foldl selStep SelSt.start
      ∈ ({SelSt.acc} : Set SelSt)
    rw [List.foldl_append, foldl_sel_inl, if_neg hP]
    show (((hash :: Z).map Sum.inr).foldl selStep SelSt.left) ∈ ({SelSt.acc} : Set SelSt)
    rw [List.map_cons, List.foldl_cons,
      show selStep SelSt.left (Sum.inr hash) = SelSt.acc from rfl, foldl_sel_acc]
    rfl
  rw [onCopy, if_pos hmem, seqFinEval_inl_append]
  rfl

lemma onCopy_start (S : List Gam) (hS : S ≠ []) :
    onCopy ((S.map Sum.inr : List (Gam ⊕ Gam)))
      = [Sym8.comma, Sym8.lpar, Sym8.lbrack] ++ runFrom SplitMode.left S := by
  classical
  obtain ⟨x, S', rfl⟩ : ∃ x S', S = x :: S' := by
    cases S with
    | nil => exact absurd rfl hS
    | cons x S' => exact ⟨x, S', rfl⟩
  have hmem : ((x :: S').map Sum.inr : List (Gam ⊕ Gam)) ∈ selLang := by
    show (((x :: S').map Sum.inr).foldl selStep SelSt.start) ∈ ({SelSt.acc} : Set SelSt)
    rw [List.map_cons, List.foldl_cons,
      show selStep SelSt.start (Sum.inr x) = SelSt.acc from rfl, foldl_sel_acc]
    rfl
  rw [onCopy, if_pos hmem]
  rfl

lemma onCopy_irrel (P S : List Gam) (hP : P ≠ []) (hS : ∀ Z, S ≠ hash :: Z) :
    onCopy (P.map Sum.inl ++ S.map Sum.inr) = [] := by
  classical
  have hmem : (P.map Sum.inl ++ S.map Sum.inr) ∉ selLang := by
    show ¬ ((P.map Sum.inl ++ S.map Sum.inr).foldl selStep SelSt.start ∈ ({SelSt.acc} : Set SelSt))
    rw [List.foldl_append, foldl_sel_inl, if_neg hP]
    cases S with
    | nil => simp
    | cons x S' =>
        have hx : x ≠ hash := fun h => hS S' (by rw [h])
        have hstep : selStep SelSt.left (Sum.inr x) = SelSt.rej := by
          cases x with
          | none => rfl
          | some y =>
              cases y with
              | none => exact absurd rfl hx
              | some c => rfl
        rw [List.map_cons, List.foldl_cons, hstep, foldl_sel_rej]
        simp
  rw [onCopy, if_neg hmem]

/-! ## The string function -/

/-- The string over `Gam` that the construction runs over: the representation with its top-level
commas marked, followed by a separator and the sentinel. -/
noncomputable def preStr (A : Ty) (w : List Sym8) : List Gam :=
  (Comb.listMarkMach.run (Comb.listMarkN A) .start w).map (some : Option Sym8 → Gam)
    ++ [hash, dollar]

open Classical in
/-- The string-to-string function of the construction. -/
noncomputable def splitsStr (A : Ty) (w : List Sym8) : List Sym8 :=
  Sym8.lbrack :: ((perSplit onCopy (preStr A w)).tail ++ [Sym8.rbrack])

/-- The pairs of the output, in the order of increasing prefix, as strings. -/
def pairStr (bs : List (List Sym8)) (j : ℕ) : List Sym8 :=
  Sym8.lpar :: (Sym8.lbrack :: (joinSep (bs.take j) ++ [Sym8.rbrack])
    ++ Sym8.comma :: (Sym8.lbrack :: (joinSep (bs.drop j) ++ [Sym8.rbrack]) ++ [Sym8.rpar]))

/-! ## Running over all the cuts -/

lemma flatten_range_succ {X : Type} (f : ℕ → List X) (n : ℕ) :
    (((List.range (n + 1)).map f).flatten)
      = f 0 ++ (((List.range n).map (fun i => f (i + 1))).flatten) := by
  rw [show List.range (n + 1) = 0 :: (List.range n).map Nat.succ from List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def]


/-- The contribution of one relevant cut: the pair of the entries that precede the cut and of
those that follow it, preceded by a comma. -/
def piece (P : List Gam) (X Y : List (List Sym8)) : List Sym8 :=
  [Sym8.comma, Sym8.lpar, Sym8.lbrack] ++ leftOut P ++ joinSep X
    ++ [Sym8.rbrack, Sym8.comma, Sym8.lbrack] ++ joinSep Y ++ [Sym8.rbrack, Sym8.rpar]

/-- The cuts inside an entry contribute nothing, so the letters of an entry can be skipped. -/
lemma perSplitFrom_letters :
    ∀ (r : List Sym8) (P : List Gam), P ≠ [] → ∀ X : List Gam,
      perSplitFrom onCopy P (r.map lett ++ X) = perSplitFrom onCopy (P ++ r.map lett) X := by
  intro r
  induction r with
  | nil => intro P _ X; simp
  | cons c r ih =>
      intro P hP X
      rw [List.map_cons, List.cons_append, perSplitFrom_cons,
        onCopy_irrel P (lett c :: (r.map lett ++ X)) hP (by
          intro Z h
          exact absurd (List.cons.inj h).1 (by simp [lett, hash])),
        ih (P ++ [lett c]) (by simp) X]
      simp

/-- **Running over the cuts of the remainder of the string**, when the underlined prefix is not
empty: the relevant cuts are the ones just before a separator. -/
lemma perSplitFrom_flat :
    ∀ (cs : List (List Sym8)), (∀ x ∈ cs.tail, x ≠ []) → ∀ P : List Gam, P ≠ [] →
      perSplitFrom onCopy P (flatStr cs ++ [dollar])
        = ((List.range cs.length).map
            (fun i => piece P (cs.take (i + 1)) (cs.drop (i + 1)))).flatten := by
  intro cs
  induction cs with
  | nil =>
      intro _ P hP
      rw [flatStr_nil, List.nil_append, perSplitFrom_cons,
        onCopy_irrel P [dollar] hP (by
          intro Z h
          exact absurd (List.cons.inj h).1 (by simp [dollar, hash])),
        perSplitFrom_nil,
        show (P ++ [dollar]).map (Sum.inl : Gam → Gam ⊕ Gam)
          = (P ++ [dollar]).map Sum.inl ++ ([] : List Gam).map Sum.inr by simp,
        onCopy_irrel (P ++ [dollar]) [] (by simp) (by intro Z h; exact absurd h (by simp))]
      simp
  | cons r cs ih =>
      intro hcs P hP
      have hcs' : ∀ x ∈ cs, x ≠ [] := hcs
      have hcstail : ∀ x ∈ cs.tail, x ≠ [] := fun x hx => hcs' x (List.mem_of_mem_tail hx)
      rw [flatStr_cons,
        show (r.map lett ++ ([hash] ++ flatStr cs)) ++ [dollar]
          = r.map lett ++ (hash :: (flatStr cs ++ [dollar])) by simp,
        perSplitFrom_letters r P hP, perSplitFrom_cons,
        onCopy_hash (P ++ r.map lett) (by simp [hP]) (flatStr cs ++ [dollar]),
        runFrom_left_hash cs hcs',
        ih hcstail (P ++ r.map lett ++ [hash]) (by simp)]
      have hfirst : [Sym8.comma, Sym8.lpar, Sym8.lbrack]
          ++ (leftOut (P ++ r.map lett)
            ++ ([Sym8.rbrack, Sym8.comma, Sym8.lbrack] ++ (joinSep cs ++ [Sym8.rbrack, Sym8.rpar])))
          = piece P [r] cs := by
        rw [piece, leftOut_append, leftOut_letters]
        simp
      have hrest : ∀ i : ℕ, i < cs.length →
          piece (P ++ r.map lett ++ [hash]) (cs.take (i + 1)) (cs.drop (i + 1))
            = piece P ((r :: cs).take (i + 2)) ((r :: cs).drop (i + 2)) := by
        intro i hi
        have hne : cs.take (i + 1) ≠ [] := by
          intro hnil
          have hlen : (cs.take (i + 1)).length = 0 := by rw [hnil]; rfl
          rw [List.length_take] at hlen
          omega
        obtain ⟨y, ys, hy⟩ : ∃ y ys, cs.take (i + 1) = y :: ys := by
          cases hcut : cs.take (i + 1) with
          | nil => exact absurd hcut hne
          | cons y ys => exact ⟨y, ys, rfl⟩
        rw [piece, piece, leftOut_append, leftOut_append, leftOut_letters, leftOut_hash]
        rw [show ((r :: cs).take (i + 2)) = r :: cs.take (i + 1) from rfl,
          show ((r :: cs).drop (i + 2)) = cs.drop (i + 1) from rfl]
        rw [hy, joinSep_cons_commaJoin, joinSep_cons_commaJoin]
        simp [commaJoin]
      rw [hfirst, show (r :: cs).length = cs.length + 1 from rfl, flatten_range_succ]
      refine congrArg₂ (· ++ ·) rfl ?_
      exact congrArg List.flatten
        (List.map_congr_left (fun i hi => hrest i (List.mem_range.1 hi)))

/-- **Running over all the cuts of the whole string.** -/
lemma perSplit_flat (cs : List (List Sym8)) (hcs : ∀ x ∈ cs, x ≠ []) (hne : cs ≠ []) :
    perSplit onCopy (flatStr cs ++ [dollar])
      = ((List.range (cs.length + 1)).map
          (fun i => piece [] (cs.take i) (cs.drop i))).flatten := by
  obtain ⟨r, cs', rfl⟩ : ∃ r cs', cs = r :: cs' := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons r cs' => exact ⟨r, cs', rfl⟩
  have hr : r ≠ [] := hcs r (by simp)
  have hcs' : ∀ x ∈ cs', x ≠ [] := fun x hx => hcs x (by simp [hx])
  obtain ⟨c, r', rfl⟩ : ∃ c r', r = c :: r' := by
    cases r with
    | nil => exact absurd rfl hr
    | cons c r' => exact ⟨c, r', rfl⟩
  have hstr : flatStr ((c :: r') :: cs') ++ [dollar]
      = lett c :: (flatStr (r' :: cs') ++ [dollar]) := by
    rw [flatStr_cons, flatStr_cons]
    simp
  rw [perSplit_eq_perSplitFrom, hstr, perSplitFrom_cons]
  rw [show ([] : List Gam).map (Sum.inl : Gam → Gam ⊕ Gam)
      ++ (lett c :: (flatStr (r' :: cs') ++ [dollar])).map Sum.inr
    = ((lett c :: (flatStr (r' :: cs') ++ [dollar])).map Sum.inr : List (Gam ⊕ Gam)) by simp,
    onCopy_start _ (by simp), ← hstr, runFrom_left_flat _ hcs (by simp),
    List.nil_append, perSplitFrom_flat (r' :: cs') hcs' [lett c] (by simp)]
  have hpiece : ∀ i : ℕ,
      piece [lett c] ((r' :: cs').take (i + 1)) ((r' :: cs').drop (i + 1))
        = piece [] (((c :: r') :: cs').take (i + 1)) (((c :: r') :: cs').drop (i + 1)) := by
    intro i
    rw [piece, piece]
    rw [show ((r' :: cs').take (i + 1)) = r' :: cs'.take i from rfl,
      show (((c :: r') :: cs').take (i + 1)) = (c :: r') :: cs'.take i from rfl,
      show ((r' :: cs').drop (i + 1)) = cs'.drop i from rfl,
      show (((c :: r') :: cs').drop (i + 1)) = cs'.drop i from rfl,
      joinSep_cons_commaJoin, joinSep_cons_commaJoin]
    show [Sym8.comma, Sym8.lpar, Sym8.lbrack] ++ leftOut [lett c] ++ _ ++ _ ++ _ ++ _
      = [Sym8.comma, Sym8.lpar, Sym8.lbrack] ++ leftOut [] ++ _ ++ _ ++ _ ++ _
    rw [show leftOut [lett c] = [c] from rfl, leftOut_nil]
    simp
  rw [show (((c :: r') :: cs').length + 1) = ((r' :: cs').length + 1) from rfl,
    flatten_range_succ]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · simp [piece]
  · exact congrArg List.flatten (List.map_congr_left (fun i _ => hpiece i))

/-- **The heart of the construction.**  Running over all the cuts of the marked representation
produces the pairs, in the order of increasing prefix, each preceded by a comma. -/
theorem perSplit_onCopy (bs : List (List Sym8)) (hbs : ∀ x ∈ bs, x ≠ []) :
    perSplit onCopy ((Comb.optBlocks bs).map (some : Option Sym8 → Gam) ++ [hash, dollar])
      = (((List.range (bs.length + 1)).map (fun j => Sym8.comma :: pairStr bs j)).flatten) := by
  have hpiece : ∀ (X Y : List (List Sym8)), piece [] X Y
      = Sym8.comma :: (Sym8.lpar :: (Sym8.lbrack :: (joinSep X ++ [Sym8.rbrack])
        ++ Sym8.comma :: (Sym8.lbrack :: (joinSep Y ++ [Sym8.rbrack]) ++ [Sym8.rpar]))) := by
    intro X Y
    rw [piece, leftOut_nil]
    simp
  by_cases hne : bs = []
  · subst hne
    classical
    have h0 : perSplit onCopy ([hash, dollar] : List Gam)
        = piece [] [] [] := by
      have e0 : onCopy (([hash, dollar] : List Gam).map Sum.inr) = piece [] [] [] := by
        rw [onCopy_start _ (by simp), piece]
        show _ = [Sym8.comma, Sym8.lpar, Sym8.lbrack] ++ [] ++ [] ++
          [Sym8.rbrack, Sym8.comma, Sym8.lbrack] ++ [] ++ [Sym8.rbrack, Sym8.rpar]
        rw [show runFrom SplitMode.left ([hash, dollar] : List Gam)
          = [Sym8.rbrack, Sym8.comma, Sym8.lbrack] ++ [Sym8.rbrack, Sym8.rpar] from rfl]
        simp
      have e1 : onCopy (([hash] : List Gam).map Sum.inl ++ ([dollar] : List Gam).map Sum.inr) = [] :=
        onCopy_irrel [hash] [dollar] (by simp) (by
          intro Z h
          exact absurd (List.cons.inj h).1 (by simp [dollar, hash]))
      have e2 : onCopy (([hash, dollar] : List Gam).map Sum.inl) = [] := by
        rw [show ([hash, dollar] : List Gam).map (Sum.inl : Gam → Gam ⊕ Gam)
          = ([hash, dollar] : List Gam).map Sum.inl ++ ([] : List Gam).map Sum.inr by simp]
        exact onCopy_irrel [hash, dollar] [] (by simp) (by intro Z h; exact absurd h (by simp))
      rw [perSplit_eq_perSplitFrom, perSplitFrom_cons, perSplitFrom_cons, perSplitFrom_nil]
      rw [show ([] : List Gam).map (Sum.inl : Gam → Gam ⊕ Gam)
          ++ ([hash, dollar] : List Gam).map Sum.inr
        = (([hash, dollar] : List Gam).map Sum.inr : List (Gam ⊕ Gam)) by simp, e0]
      rw [show ([] : List Gam) ++ [hash] = ([hash] : List Gam) from rfl, e1]
      rw [show ([hash] : List Gam) ++ [dollar] = ([hash, dollar] : List Gam) from rfl, e2]
      simp
    rw [show (Comb.optBlocks ([] : List (List Sym8))).map (some : Option Sym8 → Gam)
      ++ [hash, dollar] = ([hash, dollar] : List Gam) from rfl, h0]
    simp [hpiece, pairStr]
  · rw [show (Comb.optBlocks bs).map (some : Option Sym8 → Gam) ++ [hash, dollar]
      = ((Comb.optBlocks bs).map (some : Option Sym8 → Gam) ++ [hash]) ++ [dollar] by simp,
      optBlocks_map_some_append bs hne, perSplit_flat bs hbs hne]
    congr 1
    refine List.map_congr_left (fun i _ => ?_)
    rw [hpiece, pairStr]

end SplitsAtom

open SplitsAtom in
/-- **The new atomic function of Definition `def:polyregular-terms`, in the order of increasing
prefix, is polyregular under string representation.** -/
theorem isPolyregularUnderRepr_splitsRev (A : Ty) :
    IsPolyregularUnderRepr (A := .list A) (B := .list (.prod (.list A) (.list A)))
      (fun l => (splitsList l).reverse) := by
  classical
  refine ⟨splitsStr A, ?_, fun l => ?_⟩
  · have h1 : IsRegularFun (fun w : List Sym8 =>
        (Comb.listMarkMach.run (Comb.listMarkN A) .start w).map (some : Option Sym8 → Gam)) :=
      (Comb.isRegularFun_listMarkRun A).comp'
        (IsRegularFun.of_rational (isRationalFun_map (some : Option Sym8 → Gam))) (fun _ => rfl)
    have hpre : IsRegularFun (preStr A) :=
      isRegularFun_concat h1 (IsRegularFun.of_rational (isRationalFun_const [hash, dollar]))
    have hper : IsPolyregular (perSplit onCopy) :=
      isPolyregular_perSplit isRegularFun_onCopy onCopy_nil
    have hclose : IsRegularFun (fun w : List Sym8 => Sym8.lbrack :: (w.tail ++ [Sym8.rbrack])) := by
      have hid : IsRegularFun (fun w : List Sym8 => w) :=
        IsRegularFun.of_rational PrimeRat.rationalFun_id
      have hbr : IsRegularFun (fun w : List Sym8 => w ++ [Sym8.rbrack]) :=
        isRegularFun_concat hid (IsRegularFun.of_rational (isRationalFun_const [Sym8.rbrack]))
      exact (Comb.isRegularFun_tail.comp' hbr (fun _ => rfl)).comp'
        (IsRegularFun.of_rational (isRationalFun_cons Sym8.lbrack)) (fun _ => rfl)
    exact (((IsPolyregular.of_regular hpre).comp' hper (fun _ => rfl)).comp'
      (IsPolyregular.of_regular hclose) (fun _ => rfl)).congr (fun _ => rfl)
  · set bs : List (List Sym8) := l.map A.repr with hbsdef
    have hbs : ∀ x ∈ bs, x ≠ [] := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨c, w, hcw, -⟩ := Comb.repr_eq_cons A a
      rw [hcw]
      simp
    have hpre : preStr A ((Ty.list A).repr l)
        = (Comb.optBlocks bs).map (some : Option Sym8 → Gam) ++ [hash, dollar] := by
      rw [preStr, Comb.listMarkMach_run]
    have hmap : ((List.range (bs.length + 1)).map (fun j => Sym8.comma :: pairStr bs j))
        = (((List.range (bs.length + 1)).map (fun j => pairStr bs j)).map
            (fun x => Sym8.comma :: x)) := by
      rw [List.map_map]
      rfl
    have htail : ((perSplit onCopy (preStr A ((Ty.list A).repr l))).tail)
        = joinSep ((List.range (bs.length + 1)).map (fun j => pairStr bs j)) := by
      rw [hpre, perSplit_onCopy bs hbs, hmap]
      exact tail_commaJoin _
    have hpair : ∀ i : ℕ, (Ty.prod (Ty.list A) (Ty.list A)).repr (l.take i, l.drop i)
        = pairStr bs i := by
      intro i
      rw [Ty.repr_prod, Ty.repr_list, Ty.repr_list, pairStr, hbsdef, List.map_take,
        List.map_drop]
    show Sym8.lbrack :: ((perSplit onCopy (preStr A ((Ty.list A).repr l))).tail
      ++ [Sym8.rbrack]) = _
    rw [htail, Ty.repr_list]
    simp only [splitsList_reverse, List.map_map, Function.comp_def]
    have hlen : bs.length = l.length := by rw [hbsdef, List.length_map]
    rw [hlen]
    congr 2
    exact congrArg joinSep (List.map_congr_left (fun i _ => (hpair i).symm))

/-- **The new atomic function of Definition `def:polyregular-terms` is polyregular under string
representation.** -/
theorem isPolyregularUnderRepr_splits (A : Ty) :
    IsPolyregularUnderRepr (A := .list A) (B := .list (.prod (.list A) (.list A)))
      (fun l => splitsList l) :=
  ((isPolyregularUnderRepr_splitsRev A).comp
    (isRegularUnderRepr_reverse (.prod (.list A) (.list A))).isPolyregularUnderRepr).congr
    (fun l => List.reverse_reverse (splitsList l))

end Transducers
