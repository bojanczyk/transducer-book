/-
Part D, Section *A functional programming language*: Lemma `lem:tiling-checker`.

A higher-order polyregular term of type

    1* × ((1* × 1*) → T) → (1 + 1)

which, given a number `n` and a function `f` on the infinite quadrant, answers whether the
restriction of `f` to `{0,…,n} × {0,…,n}` is a solution of a fixed instance of the tiling problem
(`RequestProject/PartD/Tiling.lean`).

The construction is the book's: numbers are lists of units, so that zero is the empty list and
incrementation is the list constructor; the corners are checked by applying `f` to `(0,0)` and to
`(n,n)`; the prefixes function of Example `ex:all-prefixes` and the rectangle function of Example
`ex:strength-and-rectangle` produce the list of all pairs in `{0,…,n-1} × {0,…,n-1}`, which
incrementation turns into the list of all `2 × 2` windows; each window is replaced by the empty
list if it satisfies the local constraint and by a one-element list otherwise, and the answer is
whether the concatenation of those lists is empty.  (The book filters the windows and asks whether
the resulting list is empty; replacing the filter by the list-valued map that defines it, as in
Example `ex:filter`, is the same computation and saves a combinator.)

The finite set of tiles is the type `Transducers.HOTile.tileTy k`, the arrow-free higher-order type
`1 + (1 + ⋯ + 1)` with `k+1` summands, whose elements are the tiles `0, …, k` of an instance with
`maxTile = k`.
-/
import RequestProject.PartD.HOSyntax
import RequestProject.PartD.Tiling

namespace Transducers
namespace HOTile

/-! ## Booleans and natural numbers in the language -/

/-- The type of Booleans, `1 + 1`. -/
abbrev boolTy : HTy := .sum .one .one

/-- The type of natural numbers, `1*`. -/
abbrev natTy : HTy := .list .one

/-- The Boolean `true`. -/
def trueS : boolTy.Sem := Sum.inl ()

/-- The Boolean `false`. -/
def falseS : boolTy.Sem := Sum.inr ()

/-- A Boolean of Lean, as an element of `1 + 1`. -/
def ofBool : Bool → boolTy.Sem
  | true => trueS
  | false => falseS

@[simp] lemma ofBool_eq_trueS {b : Bool} : ofBool b = trueS ↔ b = true := by
  cases b <;> simp [ofBool, trueS, falseS]

@[simp] lemma ofBool_true : ofBool true = trueS := rfl

@[simp] lemma ofBool_false : ofBool false = falseS := rfl

/-- The Boolean of a value of type `1 + 1`. -/
def toB : boolTy.Sem → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

@[simp] lemma toB_ofBool (b : Bool) : toB (ofBool b) = b := by cases b <;> rfl

@[simp] lemma ofBool_toB (x : boolTy.Sem) : ofBool (toB x) = x := by
  rcases x with ⟨⟩ | ⟨⟩ <;> rfl

lemma trueS_ne_falseS : trueS ≠ falseS := by simp [trueS, falseS]

/-- A value of type `1 + 1` is `true` or `false`. -/
lemma eq_trueS_or_eq_falseS (x : boolTy.Sem) : x = trueS ∨ x = falseS := by
  rcases x with ⟨⟩ | ⟨⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The natural number `n`, as an element of `1* = List Unit`. -/
def unary (n : ℕ) : List Unit := List.replicate n ()

@[simp] lemma unary_length (n : ℕ) : (unary n).length = n := by simp [unary]

lemma unary_zero : unary 0 = [] := rfl

lemma unary_succ (n : ℕ) : unary (n + 1) = () :: unary n := rfl

/-- A list of units is determined by its length. -/
lemma eq_unary : ∀ l : List Unit, l = unary l.length
  | [] => rfl
  | a :: l => by
      cases a
      rw [List.length_cons, unary_succ]
      exact congrArg _ (eq_unary l)

/-- A prefix of a list of units is the unary representation of its length. -/
lemma take_unary (t : List Unit) {i : ℕ} (h : i ≤ t.length) : t.take i = unary i := by
  conv_lhs => rw [eq_unary t]
  simp only [unary, List.take_replicate]
  congr 1
  omega

/-! ## Some terms of the language

The evaluation lemmas below are stated in fully applied form, because that is the form in which
the semantics of a term is met: the semantics of an application `f a` is the semantics of `f`
applied to the semantics of `a`. -/

/-- The term `true`. -/
def ttT (Γ : List HTy) : HTerm Γ boolTy := (HTerm.atom (.inl .one .one)).app .unit

/-- The term `false`. -/
def ffT (Γ : List HTy) : HTerm Γ boolTy := (HTerm.atom (.inr .one .one)).app .unit

@[simp] lemma eval_ttT {Γ : List HTy} (e : HEnv Γ) : (ttT Γ).eval e = trueS := rfl

@[simp] lemma eval_ffT {Γ : List HTy} (e : HEnv Γ) : (ffT Γ).eval e = falseS := rfl

/-- Conjunction. -/
def andT (Γ : List HTy) : HTerm Γ (.arrow boolTy (.arrow boolTy boolTy)) :=
  .lam (.lam
    ((((HTerm.atom (.either .one .one boolTy)).app (.lam (.var (.succ .zero)))).app
        (.lam (ffT _))).app (.var (.succ .zero))))

/-- Disjunction. -/
def orT (Γ : List HTy) : HTerm Γ (.arrow boolTy (.arrow boolTy boolTy)) :=
  .lam (.lam
    ((((HTerm.atom (.either .one .one boolTy)).app (.lam (ttT _))).app
        (.lam (.var (.succ .zero)))).app (.var (.succ .zero))))

@[simp] lemma eval_andT {Γ : List HTy} (e : HEnv Γ) (a b : boolTy.Sem) :
    (andT Γ).eval e a b = ofBool (toB a && toB b) := by
  rcases a with ⟨⟩ | ⟨⟩ <;> rcases b with ⟨⟩ | ⟨⟩ <;> rfl

@[simp] lemma eval_orT {Γ : List HTy} (e : HEnv Γ) (a b : boolTy.Sem) :
    (orT Γ).eval e a b = ofBool (toB a || toB b) := by
  rcases a with ⟨⟩ | ⟨⟩ <;> rcases b with ⟨⟩ | ⟨⟩ <;> rfl

/-- Is the list empty? -/
def isNilT (A : HTy) (Γ : List HTy) : HTerm Γ (.arrow (.list A) boolTy) :=
  .lam ((((HTerm.atom (.either .one (.prod A (.list A)) boolTy)).app (.lam (ttT _))).app
      (.lam (ffT _))).app ((HTerm.atom (.uncons A)).app (.var .zero)))

@[simp] lemma eval_isNilT {A : HTy} {Γ : List HTy} (e : HEnv Γ) (l : List A.Sem) :
    (isNilT A Γ).eval e l = ofBool l.isEmpty := by
  cases l <;> rfl

/-- All the prefixes of a list, from the longest to the shortest: the function of Example
`ex:all-prefixes`. -/
def prefixesT (A : HTy) (Γ : List HTy) : HTerm Γ (.arrow (.list A) (.list (.list A))) :=
  .lam (((HTerm.atom (.map (.prod (.list A) (.list A)) (.list A))).app
      (.lam ((HTerm.atom (.fst (.list A) (.list A))).app (.var .zero)))).app
    ((HTerm.atom (.splits A)).app (.var .zero)))

@[simp] lemma eval_prefixesT {A : HTy} {Γ : List HTy} (e : HEnv Γ) (l : List A.Sem) :
    (prefixesT A Γ).eval e l = (splitsList l).map Prod.fst := rfl

/-- The numbers `0, …, n-1`, as a list of lists of units. -/
def smalls : List Unit → List (List Unit)
  | [] => []
  | _ :: t => (splitsList t).map Prod.fst

/-- The numbers `0, …, n-1`; the empty list when `n` is zero. -/
def smallsT (Γ : List HTy) : HTerm Γ (.arrow natTy (.list natTy)) :=
  .lam ((((HTerm.atom (.either .one (.prod .one natTy) (.list natTy))).app (.lam .nil)).app
      (.lam ((prefixesT .one _).app ((HTerm.atom (.snd .one natTy)).app (.var .zero))))).app
    ((HTerm.atom (.uncons .one)).app (.var .zero)))

@[simp] lemma eval_smallsT {Γ : List HTy} (e : HEnv Γ) (l : List Unit) :
    (smallsT Γ).eval e l = smalls l := by
  cases l <;> rfl

lemma mem_smalls (n : List Unit) (x : List Unit) :
    x ∈ smalls n ↔ ∃ i < n.length, x = unary i := by
  cases n with
  | nil => simp [smalls]
  | cons a t =>
      constructor
      · intro hx
        simp only [smalls, List.mem_map, splitsList, List.mem_reverse, List.mem_range] at hx
        obtain ⟨p, ⟨i, hi, rfl⟩, rfl⟩ := hx
        simp only [List.length_cons]
        exact ⟨i, by omega, take_unary t (by omega)⟩
      · rintro ⟨i, hi, rfl⟩
        simp only [List.length_cons] at hi
        simp only [smalls, List.mem_map, splitsList, List.mem_reverse, List.mem_range]
        exact ⟨(t.take i, t.drop i), ⟨i, by omega, rfl⟩, take_unary t (by omega)⟩

/-- The pairs of elements of two lists, ordered lexicographically: the rectangle function of
Example `ex:strength-and-rectangle`. -/
def rectT (A B : HTy) (Γ : List HTy) :
    HTerm Γ (.arrow (.list A) (.arrow (.list B) (.list (.prod A B)))) :=
  .lam (.lam ((HTerm.atom (.concat (.prod A B))).app
    (((HTerm.atom (.map A (.list (.prod A B)))).app
        (.lam (((HTerm.atom (.map B (.prod A B))).app
            (.lam (.pair (.var (.succ .zero)) (.var .zero)))).app (.var (.succ .zero))))).app
      (.var (.succ .zero)))))

@[simp] lemma eval_rectT {A B : HTy} {Γ : List HTy} (e : HEnv Γ)
    (l1 : List A.Sem) (l2 : List B.Sem) :
    (rectT A B Γ).eval e l1 l2 = (l1.map (fun a => l2.map (fun b => (a, b)))).flatten := rfl

/-- All the pairs in `{0,…,n-1} × {0,…,n-1}`. -/
def pairsOf (n : List Unit) : List (List Unit × List Unit) :=
  ((smalls n).map (fun a => (smalls n).map (fun b => (a, b)))).flatten

lemma mem_pairsOf (n : List Unit) (p : List Unit × List Unit) :
    p ∈ pairsOf n ↔ ∃ i < n.length, ∃ j < n.length, p = (unary i, unary j) := by
  obtain ⟨a, b⟩ := p
  simp only [pairsOf, List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨l, ⟨a', ha', rfl⟩, hb⟩
    obtain ⟨b', hb', hab⟩ := List.mem_map.1 hb
    obtain ⟨i, hi, rfl⟩ := (mem_smalls n a').1 ha'
    obtain ⟨j, hj, rfl⟩ := (mem_smalls n b').1 hb'
    exact ⟨i, hi, j, hj, hab.symm⟩
  · rintro ⟨i, hi, j, hj, hab⟩
    rw [Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨(smalls n).map (fun b => (unary i, b)),
      ⟨unary i, (mem_smalls n _).2 ⟨i, hi, rfl⟩, rfl⟩,
      List.mem_map.2 ⟨unary j, (mem_smalls n _).2 ⟨j, hj, rfl⟩, rfl⟩⟩

/-! ## The tiles -/

/-- The type of the tiles `0, …, k`: the arrow-free type `1 + (1 + ⋯ + 1)` with `k+1`
summands. -/
def tileTy : ℕ → HTy
  | 0 => .one
  | k + 1 => .sum .one (tileTy k)

/-- The tile with index `i`; indices larger than `k` are clamped to `k`. -/
def tileOfNat : (k : ℕ) → ℕ → (tileTy k).Sem
  | 0, _ => ()
  | _ + 1, 0 => Sum.inl ()
  | k + 1, i + 1 => Sum.inr (tileOfNat k i)

/-- The index of a tile. -/
def tileIdx : (k : ℕ) → (tileTy k).Sem → ℕ
  | 0, _ => 0
  | _ + 1, Sum.inl _ => 0
  | k + 1, Sum.inr x => tileIdx k x + 1

instance tileDecEq : (k : ℕ) → DecidableEq (tileTy k).Sem
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 => letI := tileDecEq k; inferInstanceAs (DecidableEq (Unit ⊕ (tileTy k).Sem))

lemma tileIdx_le : ∀ (k : ℕ) (x : (tileTy k).Sem), tileIdx k x ≤ k
  | 0, _ => Nat.le_refl 0
  | _ + 1, Sum.inl _ => Nat.zero_le _
  | k + 1, Sum.inr x => Nat.succ_le_succ (tileIdx_le k x)

@[simp] lemma tileOfNat_tileIdx : ∀ (k : ℕ) (x : (tileTy k).Sem),
    tileOfNat k (tileIdx k x) = x
  | 0, x => by cases x; rfl
  | _ + 1, Sum.inl u => by cases u; rfl
  | k + 1, Sum.inr x => congrArg Sum.inr (tileOfNat_tileIdx k x)

lemma tileIdx_tileOfNat : ∀ (k i : ℕ), i ≤ k → tileIdx k (tileOfNat k i) = i
  | 0, 0, _ => rfl
  | 0, _ + 1, h => absurd h (by omega)
  | _ + 1, 0, _ => rfl
  | k + 1, i + 1, h => congrArg (· + 1) (tileIdx_tileOfNat k i (by omega))

/-- A tile is the tile of index `i` exactly when its index is `i`. -/
lemma eq_tileOfNat_iff {k i : ℕ} (hi : i ≤ k) (x : (tileTy k).Sem) :
    x = tileOfNat k i ↔ tileIdx k x = i := by
  constructor
  · rintro rfl
    exact tileIdx_tileOfNat k i hi
  · rintro rfl
    exact (tileOfNat_tileIdx k x).symm

/-- The term for the tile with index `i`. -/
def tileLit : (k i : ℕ) → (Γ : List HTy) → HTerm Γ (tileTy k)
  | 0, _, _ => .unit
  | k + 1, 0, _ => (HTerm.atom (.inl .one (tileTy k))).app .unit
  | k + 1, i + 1, Γ => (HTerm.atom (.inr .one (tileTy k))).app (tileLit k i Γ)

@[simp] lemma eval_tileLit : ∀ (k i : ℕ) {Γ : List HTy} (e : HEnv Γ),
    (tileLit k i Γ).eval e = tileOfNat k i
  | 0, _, _, _ => rfl
  | _ + 1, 0, _, _ => rfl
  | k + 1, i + 1, _, e => congrArg Sum.inr (eval_tileLit k i e)

/-- Equality of tiles. -/
def tileEqT : (k : ℕ) → (Γ : List HTy) →
    HTerm Γ (.arrow (tileTy k) (.arrow (tileTy k) boolTy))
  | 0, _ => .lam (.lam (ttT _))
  | k + 1, _ => .lam (.lam
      ((((HTerm.atom (.either .one (tileTy k) boolTy)).app
          (.lam ((((HTerm.atom (.either .one (tileTy k) boolTy)).app (.lam (ttT _))).app
              (.lam (ffT _))).app (.var (.succ .zero))))).app
        (.lam ((((HTerm.atom (.either .one (tileTy k) boolTy)).app (.lam (ffT _))).app
            (.lam (((tileEqT k _).app (.var (.succ .zero))).app (.var .zero)))).app
          (.var (.succ .zero))))).app
        (.var (.succ .zero))))

@[simp] lemma eval_tileEqT : ∀ (k : ℕ) {Γ : List HTy} (e : HEnv Γ) (a b : (tileTy k).Sem),
    (tileEqT k Γ).eval e a b = ofBool (decide (a = b))
  | 0, _, _, a, b => by cases a; cases b; rfl
  | k + 1, _, e, a, b => by
      rcases a with ⟨⟩ | a <;> rcases b with ⟨⟩ | b
      · rfl
      · rfl
      · rfl
      · show (tileEqT k _).eval
            (HEnv.cons (A := tileTy k) b (HEnv.cons (A := tileTy k) a
              (HEnv.cons (A := tileTy (k + 1)) (Sum.inr b)
                (HEnv.cons (A := tileTy (k + 1)) (Sum.inr a) e)))) a b = _
        rw [eval_tileEqT k]
        congr 1
        rw [decide_eq_decide]
        constructor
        · rintro rfl; rfl
        · intro h; cases h; rfl

/-! ## The windows -/

/-- The type of a `2 × 2` window: the four tiles
`(f(i,j), f(i+1,j), f(i,j+1), f(i+1,j+1))`. -/
def winTy (k : ℕ) : HTy :=
  .prod (tileTy k) (.prod (tileTy k) (.prod (tileTy k) (tileTy k)))

/-- The window described by a quadruple of tile indices. -/
def winOf (k : ℕ) (c : ℕ × ℕ × ℕ × ℕ) : (winTy k).Sem :=
  (tileOfNat k c.1, tileOfNat k c.2.1, tileOfNat k c.2.2.1, tileOfNat k c.2.2.2)

instance winDecEq (k : ℕ) : DecidableEq (winTy k).Sem :=
  inferInstanceAs (DecidableEq ((tileTy k).Sem × (tileTy k).Sem × (tileTy k).Sem × (tileTy k).Sem))

/-- A window satisfies the local constraint exactly when the quadruple of the indices of its
tiles occurs in it. -/
lemma mem_map_winOf_iff {k : ℕ} {cs : List (ℕ × ℕ × ℕ × ℕ)}
    (hcs : ∀ c ∈ cs, c.1 ≤ k ∧ c.2.1 ≤ k ∧ c.2.2.1 ≤ k ∧ c.2.2.2 ≤ k)
    (w : (winTy k).Sem) :
    w ∈ cs.map (winOf k) ↔
      (tileIdx k w.1, tileIdx k w.2.1, tileIdx k w.2.2.1, tileIdx k w.2.2.2) ∈ cs := by
  obtain ⟨a, b, c, d⟩ := w
  constructor
  · intro hw
    obtain ⟨u, hu, hwu⟩ := List.mem_map.1 hw
    obtain ⟨h1, h2, h3, h4⟩ := hcs u hu
    simp only [winOf] at hwu
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hwu
    rw [tileIdx_tileOfNat k _ h1, tileIdx_tileOfNat k _ h2, tileIdx_tileOfNat k _ h3,
      tileIdx_tileOfNat k _ h4]
    exact hu
  · intro hq
    refine List.mem_map.2 ⟨_, hq, ?_⟩
    simp [winOf]

/-- Is the window the given one? -/
def eqWinT (k : ℕ) (c : ℕ × ℕ × ℕ × ℕ) (Γ : List HTy) : HTerm Γ (.arrow (winTy k) boolTy) :=
  HTerm.lam
    (HTerm.app
      (HTerm.app (andT _)
        (HTerm.app
          (HTerm.app (tileEqT k _)
            (HTerm.app (HTerm.atom (.fst (tileTy k) _)) (HTerm.var .zero)))
          (tileLit k c.1 _)))
      (HTerm.app
        (HTerm.app (andT _)
          (HTerm.app
            (HTerm.app (tileEqT k _)
              (HTerm.app (HTerm.atom (.fst (tileTy k) _))
                (HTerm.app (HTerm.atom (.snd (tileTy k) _)) (HTerm.var .zero))))
            (tileLit k c.2.1 _)))
        (HTerm.app
          (HTerm.app (andT _)
            (HTerm.app
              (HTerm.app (tileEqT k _)
                (HTerm.app (HTerm.atom (.fst (tileTy k) (tileTy k)))
                  (HTerm.app (HTerm.atom (.snd (tileTy k) _))
                    (HTerm.app (HTerm.atom (.snd (tileTy k) _)) (HTerm.var .zero)))))
              (tileLit k c.2.2.1 _)))
          (HTerm.app
            (HTerm.app (tileEqT k _)
              (HTerm.app (HTerm.atom (.snd (tileTy k) (tileTy k)))
                (HTerm.app (HTerm.atom (.snd (tileTy k) _))
                  (HTerm.app (HTerm.atom (.snd (tileTy k) _)) (HTerm.var .zero)))))
            (tileLit k c.2.2.2 _)))))

@[simp] lemma eval_eqWinT (k : ℕ) (c : ℕ × ℕ × ℕ × ℕ) {Γ : List HTy} (e : HEnv Γ)
    (w : (winTy k).Sem) :
    (eqWinT k c Γ).eval e w = ofBool (decide (w = winOf k c)) := by
  obtain ⟨a, b, c1, d⟩ := w
  simp only [eqWinT, HTerm.eval_lam, HTerm.eval_app, HTerm.eval_atom, HTerm.eval_var,
    HVar.lookup, HAtom.sem, eval_andT, eval_tileEqT, eval_tileLit, toB_ofBool]
  congr 1
  have key : ((a, b, c1, d) = winOf k c) ↔ (a = tileOfNat k c.1 ∧ b = tileOfNat k c.2.1 ∧
      c1 = tileOfNat k c.2.2.1 ∧ d = tileOfNat k c.2.2.2) := by
    constructor
    · intro h
      exact ⟨congrArg (fun z => z.1) h, congrArg (fun z => z.2.1) h,
        congrArg (fun z => z.2.2.1) h, congrArg (fun z => z.2.2.2) h⟩
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      rfl
  rw [decide_eq_decide.2 key, Bool.decide_and, Bool.decide_and, Bool.decide_and]

/-- Does the window satisfy the local constraint? -/
def inCT (k : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → (Γ : List HTy) → HTerm Γ (.arrow (winTy k) boolTy)
  | [], _ => .lam (ffT _)
  | c :: cs, _ =>
      .lam (((orT _).app ((eqWinT k c _).app (.var .zero))).app ((inCT k cs _).app (.var .zero)))

@[simp] lemma eval_inCT (k : ℕ) : ∀ (cs : List (ℕ × ℕ × ℕ × ℕ)) {Γ : List HTy} (e : HEnv Γ)
    (w : (winTy k).Sem),
    (inCT k cs Γ).eval e w = ofBool (decide (w ∈ cs.map (winOf k)))
  | [], _, _, w => by simp [inCT, ofBool]
  | c :: cs, _, e, w => by
      simp only [inCT, HTerm.eval_lam, HTerm.eval_app, HTerm.eval_var, HVar.lookup,
        eval_orT, eval_eqWinT, eval_inCT k cs (HEnv.cons w e) w, toB_ofBool]
      by_cases h1 : w = winOf k c <;> by_cases h2 : w ∈ cs.map (winOf k) <;>
        simp [h1, h2]

/-! ## The checker -/

/-- The input type of the term of Lemma `lem:tiling-checker`: a number and a function on the
infinite quadrant. -/
def inTy (k : ℕ) : HTy := .prod natTy (.arrow (.prod natTy natTy) (tileTy k))

/-- The size argument of the input. -/
def nvar (k : ℕ) {Γ : List HTy} (x : HTerm Γ (inTy k)) : HTerm Γ natTy :=
  (HTerm.atom (.fst natTy (.arrow (.prod natTy natTy) (tileTy k)))).app x

/-- The function argument of the input. -/
def fvar (k : ℕ) {Γ : List HTy} (x : HTerm Γ (inTy k)) :
    HTerm Γ (.arrow (.prod natTy natTy) (tileTy k)) :=
  (HTerm.atom (.snd natTy (.arrow (.prod natTy natTy) (tileTy k)))).app x

/-- The window at a pair `(i,j)`, with the input in the context. -/
def winFunT (k : ℕ) : HTerm [inTy k] (.arrow (.prod natTy natTy) (winTy k)) :=
  .lam
    (.pair
      ((fvar k (.var (.succ .zero))).app
        (.pair ((HTerm.atom (.fst natTy natTy)).app (.var .zero))
          ((HTerm.atom (.snd natTy natTy)).app (.var .zero))))
      (.pair
        ((fvar k (.var (.succ .zero))).app
          (.pair (.cons .unit ((HTerm.atom (.fst natTy natTy)).app (.var .zero)))
            ((HTerm.atom (.snd natTy natTy)).app (.var .zero))))
        (.pair
          ((fvar k (.var (.succ .zero))).app
            (.pair ((HTerm.atom (.fst natTy natTy)).app (.var .zero))
              (.cons .unit ((HTerm.atom (.snd natTy natTy)).app (.var .zero)))))
          ((fvar k (.var (.succ .zero))).app
            (.pair (.cons .unit ((HTerm.atom (.fst natTy natTy)).app (.var .zero)))
              (.cons .unit ((HTerm.atom (.snd natTy natTy)).app (.var .zero))))))))

/-- The window at a pair of numbers. -/
def winAt {k : ℕ} (f : List Unit × List Unit → (tileTy k).Sem)
    (p : List Unit × List Unit) : (winTy k).Sem :=
  (f p, f (() :: p.1, p.2), f (p.1, () :: p.2), f (() :: p.1, () :: p.2))

@[simp] lemma eval_winFunT (k : ℕ) (n : List Unit)
    (f : List Unit × List Unit → (tileTy k).Sem) :
    (winFunT k).eval (HEnv.cons (n, f) .nil) = winAt f := rfl

/-- The empty list if the window satisfies the local constraint, a one-element list
otherwise. -/
def badFunT (k : ℕ) (cs : List (ℕ × ℕ × ℕ × ℕ)) (Γ : List HTy) :
    HTerm Γ (.arrow (winTy k) (.list .one)) :=
  .lam ((((HTerm.atom (.either .one .one (.list .one))).app (.lam .nil)).app
      (.lam (.cons .unit .nil))).app ((inCT k cs _).app (.var .zero)))

/-- The value of `badFunT` at a window. -/
lemma eval_badFunT_apply (k : ℕ) (cs : List (ℕ × ℕ × ℕ × ℕ)) {Γ : List HTy} (e : HEnv Γ)
    (w : (winTy k).Sem) :
    (badFunT k cs Γ).eval e w = if w ∈ cs.map (winOf k) then ([] : List Unit) else [()] := by
  show (Sum.elim (fun _ => []) (fun _ => [()]) ((inCT k cs _).eval (HEnv.cons w e) w) :
    List Unit) = _
  rw [eval_inCT k cs (HEnv.cons w e) w]
  by_cases h : w ∈ cs.map (winOf k) <;> simp [h, ofBool, trueS, falseS]

@[simp] lemma eval_badFunT (k : ℕ) (cs : List (ℕ × ℕ × ℕ × ℕ)) {Γ : List HTy} (e : HEnv Γ) :
    (badFunT k cs Γ).eval e =
      fun w => if w ∈ cs.map (winOf k) then ([] : List Unit) else [()] :=
  funext (eval_badFunT_apply k cs e)

/-- The list of all the `2 × 2` windows of the grid, with the input in the context. -/
def windowsT (k : ℕ) : HTerm [inTy k] (.list (winTy k)) :=
  HTerm.app (HTerm.app (HTerm.atom (.map (.prod natTy natTy) (winTy k))) (winFunT k))
    (HTerm.app
      (HTerm.app (rectT natTy natTy _) (HTerm.app (smallsT _) (nvar k (HTerm.var .zero))))
      (HTerm.app (smallsT _) (nvar k (HTerm.var .zero))))

/-- One unit for every window that violates the local constraint. -/
def badsT (I : Tiling.Instance) : HTerm [inTy I.maxTile] (.list .one) :=
  HTerm.app (HTerm.atom (.concat .one))
    (HTerm.app
      (HTerm.app (HTerm.atom (.map (winTy I.maxTile) (.list .one)))
        (badFunT I.maxTile I.constraint _))
      (windowsT I.maxTile))

/-- **The term of Lemma `lem:tiling-checker`**, for an instance of the tiling problem. -/
def checkTerm (I : Tiling.Instance) : HTerm [] (.arrow (inTy I.maxTile) boolTy) :=
  HTerm.lam
    (HTerm.app
      (HTerm.app (andT _)
        (HTerm.app
          (HTerm.app (tileEqT I.maxTile _)
            (HTerm.app (fvar I.maxTile (HTerm.var .zero)) (HTerm.pair .nil .nil)))
          (tileLit I.maxTile I.s _)))
      (HTerm.app
        (HTerm.app (andT _)
          (HTerm.app
            (HTerm.app (tileEqT I.maxTile _)
              (HTerm.app (fvar I.maxTile (HTerm.var .zero))
                (HTerm.pair (nvar I.maxTile (HTerm.var .zero))
                  (nvar I.maxTile (HTerm.var .zero)))))
            (tileLit I.maxTile I.t _)))
        (HTerm.app (isNilT .one _) (badsT I))))

/-- The grid of tile indices described by a function on the infinite quadrant. -/
def gridOf (k : ℕ) (f : List Unit × List Unit → (tileTy k).Sem) : ℕ → ℕ → ℕ :=
  fun i j => tileIdx k (f (unary i, unary j))

/-- **The value of the term of Lemma `lem:tiling-checker`.** -/
lemma eval_checkTerm_val (I : Tiling.Instance) (n : List Unit)
    (f : List Unit × List Unit → (tileTy I.maxTile).Sem) :
    (checkTerm I).eval .nil (n, f) =
      ofBool (decide (f ([], []) = tileOfNat I.maxTile I.s) &&
        (decide (f (n, n) = tileOfNat I.maxTile I.t) &&
          ((pairsOf n).map (fun p =>
              if winAt f p ∈ I.constraint.map (winOf I.maxTile) then ([] : List Unit)
              else [()])).flatten.isEmpty)) := by
  simp only [checkTerm, HTerm.eval_lam, HTerm.eval_app, HTerm.eval_atom, HTerm.eval_var,
    HTerm.eval_pair, HTerm.eval_nil, HVar.lookup, HAtom.sem, fvar, nvar,
    eval_andT, eval_tileEqT, eval_tileLit, eval_isNilT, eval_rectT, eval_smallsT,
    eval_badFunT, eval_winFunT, toB_ofBool, List.map_map, Function.comp_def, pairsOf,
    checkTerm, badsT, windowsT]
  rfl

/-- **Lemma `lem:tiling-checker`, in the form in which it is proved.**  The term
`Transducers.HOTile.checkTerm` answers whether the restriction of `f` to the square
`{0,…,n} × {0,…,n}` is a solution of the instance. -/
theorem eval_checkTerm (I : Tiling.Instance) (hI : I.WF) (n : List Unit)
    (f : List Unit × List Unit → (tileTy I.maxTile).Sem) :
    (checkTerm I).eval .nil (n, f) = trueS ↔
      Tiling.IsSolution I n.length (gridOf I.maxTile f) := by
  rw [eval_checkTerm_val, ofBool_eq_trueS, Bool.and_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, decide_eq_true_eq, eq_tileOfNat_iff hI.s_le, eq_tileOfNat_iff hI.t_le]
  have hwin : ∀ p : List Unit × List Unit,
      (winAt f p ∈ I.constraint.map (winOf I.maxTile)) ↔
        (tileIdx I.maxTile (f p), tileIdx I.maxTile (f (() :: p.1, p.2)),
          tileIdx I.maxTile (f (p.1, () :: p.2)),
          tileIdx I.maxTile (f (() :: p.1, () :: p.2))) ∈ I.constraint := fun p =>
    mem_map_winOf_iff hI.constraint_le _
  have hflat : (((pairsOf n).map (fun p =>
        if winAt f p ∈ I.constraint.map (winOf I.maxTile) then ([] : List Unit)
        else [()])).flatten.isEmpty = true) ↔
      ∀ p ∈ pairsOf n, winAt f p ∈ I.constraint.map (winOf I.maxTile) := by
    simp only [List.isEmpty_iff, List.flatten_eq_nil_iff, List.mem_map]
    constructor
    · intro h p hp
      by_contra hc
      exact absurd (h _ ⟨p, hp, rfl⟩) (by simp [hc])
    · rintro h l ⟨p, hp, rfl⟩
      simp [h p hp]
  rw [hflat]
  have hn : n = unary n.length := eq_unary n
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i _ j _ => tileIdx_le _ _, h1, ?_, ?_⟩
    · rw [gridOf, ← hn]; exact h2
    · intro i hi j hj
      have hp : (unary i, unary j) ∈ pairsOf n := (mem_pairsOf n _).2 ⟨i, hi, j, hj, rfl⟩
      have := (hwin _).1 (h3 _ hp)
      simpa [gridOf, unary_succ] using this
  · rintro ⟨-, h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [gridOf, ← hn] at h2; exact h2
    · intro p hp
      obtain ⟨i, hi, j, hj, rfl⟩ := (mem_pairsOf n p).1 hp
      refine (hwin _).2 ?_
      simpa [gridOf, unary_succ] using h3 i hi j hj

/-! ## The constant `false` term -/

/-- The term that answers `false` whatever its input. -/
def falseTerm (k : ℕ) : HTerm [] (.arrow (inTy k) boolTy) := .lam (ffT _)

@[simp] lemma eval_falseTerm (k : ℕ) (x : (inTy k).Sem) :
    (falseTerm k).eval .nil x = falseS := rfl

/-- **The reduction.**  The term of Lemma `lem:tiling-checker` is equivalent to the constant
`false` term exactly when the instance has no solution. -/
theorem checkTerm_eq_falseTerm_iff (I : Tiling.Instance) (hI : I.WF) :
    (checkTerm I).eval .nil = (falseTerm I.maxTile).eval .nil ↔ ¬ Tiling.Solvable I := by
  constructor
  · rintro h ⟨n, g, hg⟩
    set f : List Unit × List Unit → (tileTy I.maxTile).Sem :=
      fun p => tileOfNat I.maxTile (g p.1.length p.2.length) with hf
    have hgrid : ∀ i ≤ n, ∀ j ≤ n, gridOf I.maxTile f i j = g i j := by
      intro i hi j hj
      simp only [gridOf, hf, unary_length]
      exact tileIdx_tileOfNat _ _ (hg.tile i hi j hj)
    have hsol : Tiling.IsSolution I (unary n).length (gridOf I.maxTile f) := by
      rw [unary_length]
      refine ⟨fun i _ j _ => tileIdx_le _ _, ?_, ?_, ?_⟩
      · rw [hgrid 0 (Nat.zero_le n) 0 (Nat.zero_le n)]; exact hg.corner_s
      · rw [hgrid n le_rfl n le_rfl]; exact hg.corner_t
      · intro i hi j hj
        rw [hgrid i (by omega) j (by omega), hgrid (i + 1) (by omega) j (by omega),
          hgrid i (by omega) (j + 1) (by omega), hgrid (i + 1) (by omega) (j + 1) (by omega)]
        exact hg.window i hi j hj
    have hval := (eval_checkTerm I hI (unary n) f).2 hsol
    rw [h] at hval
    exact trueS_ne_falseS (by rw [← hval]; rfl)
  · intro h
    funext x
    obtain ⟨n, f⟩ := x
    rcases eq_trueS_or_eq_falseS ((checkTerm I).eval .nil (n, f)) with hx | hx
    · exact absurd ⟨n.length, _, (eval_checkTerm I hI n f).1 hx⟩ h
    · rw [hx]; rfl

end HOTile
end Transducers
