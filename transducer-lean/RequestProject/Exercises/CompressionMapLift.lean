/-
Claim `claim:map-compression` of the solution of Exercise `exer:regular-compression` of the chapter
*Regular functions, introduction* (`regular-intro.tex`) of *Transducers* (M. Bojańczyk):
compatibility with compression is preserved by map lifting (Definition `def:map-lifting`).

Write `#` for the separator (`none`).  A string `u` over the extended alphabet is cut by its
separators into blocks; write `P u` for the first block, `S u` for the last one, and `M u` for the
part of `mapLift f u` strictly between the image of the first block and the image of the last one,
separators included -- so that

  `mapLift f u = f(P u) ++ M u ++ f(S u)`   (the last summand being absent when `u` has no `#`).

These three quantities are compositional:

  `P (u ++ v) = P u ++ (P v if u has no #)`,
  `S (u ++ v) = (S u if v has no #) ++ S v`,
  `M (u ++ v) = M u ++ f(S u ++ P v) ++ M v`  when both `u` and `v` contain a `#`,

and `M (u ++ v)` is `M u`, or `M v`, or empty when one of them does not.  So the compression of the
image is built in two passes over the given compression: one pass computes a compression whose rules
have the values `P` and `S` of every rule of the given compression, and the second pass computes the
values `M`, using the *hypothesis* on `f` to compress the junction blocks `S u ++ P v` -- one
application of the hypothesis per rule, which is what keeps the size polynomial.
-/
import RequestProject.Exercises.CompressionSLP
import RequestProject.PartA.MapLift

namespace Transducers
namespace Exercises

variable {A B : Type}

/-! ## The first block, the last block and the middle -/

/-- The string contains a separator. -/
def hasSep : List (Option A) → Bool
  | [] => false
  | none :: _ => true
  | some _ :: w => hasSep w

/-- The first block of the string: the letters before the first separator. -/
def preBlk : List (Option A) → List A
  | [] => []
  | none :: _ => []
  | some a :: w => a :: preBlk w

/-- The last block of the string: the letters after the last separator. -/
def sufBlk : List (Option A) → List A
  | [] => []
  | none :: w => sufBlk w
  | some a :: w => if hasSep w then sufBlk w else a :: sufBlk w

/-- The middle of the image of the string under the lifting of `f`: what stands between the image
of the first block and the image of the last one, the separators around it included. -/
def midB (f : List A → List B) : List (Option A) → List (Option B)
  | [] => []
  | none :: w => none :: (if hasSep w then (f (preBlk w)).map some ++ midB f w else [])
  | some _ :: w => midB f w

@[simp] lemma hasSep_nil : hasSep ([] : List (Option A)) = false := rfl
@[simp] lemma preBlk_nil : preBlk ([] : List (Option A)) = [] := rfl
@[simp] lemma sufBlk_nil : sufBlk ([] : List (Option A)) = [] := rfl

lemma hasSep_append (u v : List (Option A)) : hasSep (u ++ v) = (hasSep u || hasSep v) := by
  induction u with
  | nil => simp [hasSep]
  | cons x u ih => cases x <;> simp [hasSep, ih]

lemma preBlk_append (u v : List (Option A)) :
    preBlk (u ++ v) = preBlk u ++ (if hasSep u then [] else preBlk v) := by
  induction u with
  | nil => simp [preBlk]
  | cons x u ih =>
      cases x with
      | none => simp [preBlk, hasSep]
      | some a => simp [preBlk, hasSep, ih]

lemma sufBlk_append (u v : List (Option A)) :
    sufBlk (u ++ v) = (if hasSep v then [] else sufBlk u) ++ sufBlk v := by
  induction u with
  | nil => cases hasSep v <;> simp [sufBlk]
  | cons x u ih =>
      cases x with
      | none => simp [sufBlk, ih]
      | some a =>
          simp only [List.cons_append, sufBlk, hasSep_append, ih]
          cases h : hasSep u <;> cases h' : hasSep v <;> simp

lemma sufBlk_eq_preBlk {u : List (Option A)} (h : hasSep u = false) : sufBlk u = preBlk u := by
  induction u with
  | nil => rfl
  | cons x u ih =>
      cases x with
      | none => simp [hasSep] at h
      | some a =>
          have h' : hasSep u = false := by simpa [hasSep] using h
          simp [sufBlk, preBlk, h', ih h']

lemma midB_eq_nil {f : List A → List B} {u : List (Option A)} (h : hasSep u = false) :
    midB f u = [] := by
  induction u with
  | nil => rfl
  | cons x u ih =>
      cases x with
      | none => simp [hasSep] at h
      | some a =>
          have h' : hasSep u = false := by simpa [hasSep] using h
          simp [midB, ih h']

/-- The middle of a concatenation. -/
lemma midB_append (f : List A → List B) (u v : List (Option A)) :
    midB f (u ++ v) =
      (if hasSep u then
        (if hasSep v then midB f u ++ (f (sufBlk u ++ preBlk v)).map some ++ midB f v
          else midB f u)
      else (if hasSep v then midB f v else [])) := by
  induction u with
  | nil =>
      cases h : hasSep v with
      | false => simp [hasSep, midB_eq_nil h]
      | true => simp [hasSep]
  | cons x u ih =>
      cases x with
      | none =>
          simp only [List.cons_append, midB, hasSep, if_true, hasSep_append, ih]
          cases hu : hasSep u with
          | false =>
              cases hv : hasSep v with
              | false => simp
              | true => simp [hu, preBlk_append, sufBlk, sufBlk_eq_preBlk hu]
          | true =>
              cases hv : hasSep v with
              | false => simp [hu, preBlk_append]
              | true => simp [hu, preBlk_append, sufBlk]
      | some a =>
          simp only [List.cons_append, midB, hasSep, ih, sufBlk]
          cases hu : hasSep u <;> cases hv : hasSep v <;> simp

/-! ## The decomposition of the image -/

/-- The image of the blocks other than the first one, with their separators. -/
def restB (f : List A → List B) (u : List (Option A)) : List (Option B) :=
  ((splitSep u).tail.map (fun b => (none : Option B) :: (f b).map some)).flatten

lemma splitSep_headI (u : List (Option A)) : (splitSep u).headI = preBlk u := by
  induction u with
  | nil => rfl
  | cons x u ih =>
      cases x with
      | none => rfl
      | some a =>
          rcases h : splitSep u with _ | ⟨b, bs⟩
          · exact absurd h (splitSep_ne_nil u)
          · have hs : splitSep (some a :: u) = (a :: b) :: bs := by rw [splitSep, h]
            have hb : b = preBlk u := by rw [h] at ih; simpa using ih
            rw [hs]
            simp [preBlk, hb]

lemma splitSep_tail_cons_some (a : A) (u : List (Option A)) :
    (splitSep (some a :: u)).tail = (splitSep u).tail := by
  rcases h : splitSep u with _ | ⟨b, bs⟩
  · exact absurd h (splitSep_ne_nil u)
  · have hs : splitSep (some a :: u) = (a :: b) :: bs := by rw [splitSep, h]
    rw [hs]
    rfl

@[simp] lemma restB_nil (f : List A → List B) : restB f [] = [] := by
  simp [restB, splitSep]

lemma restB_cons_some (f : List A → List B) (a : A) (u : List (Option A)) :
    restB f (some a :: u) = restB f u := by
  rw [restB, restB, splitSep_tail_cons_some]

lemma restB_cons_none (f : List A → List B) (u : List (Option A)) :
    restB f (none :: u) = none :: ((f (preBlk u)).map some ++ restB f u) := by
  rcases h : splitSep u with _ | ⟨b, bs⟩
  · exact absurd h (splitSep_ne_nil u)
  · have hb : b = preBlk u := by
      have := splitSep_headI u
      rw [h] at this
      simpa using this
    show (((splitSep (none :: u)).tail).map _).flatten = _
    rw [show splitSep (none :: u) = [] :: splitSep u from rfl, h]
    simp only [List.tail_cons, List.map_cons, List.flatten_cons, restB, h, List.tail_cons]
    rw [hb]
    simp

/-- The image of the string, cut into the image of the first block and the rest. -/
lemma mapLift_eq_preBlk_restB (f : List A → List B) (u : List (Option A)) :
    mapLift f u = (f (preBlk u)).map some ++ restB f u := by
  rw [mapLift, restB, ← splitSep_headI]
  generalize hbs : splitSep u = bs
  have hne : bs ≠ [] := by rw [← hbs]; exact splitSep_ne_nil u
  clear hbs
  rcases bs with _ | ⟨b, bs⟩
  · exact absurd rfl hne
  · clear hne
    induction bs generalizing b with
    | nil => simp [List.intercalate]
    | cons b' bs ih =>
        rw [List.map_cons, intercalate_cons_cons _ _ _ (by simp)]
        rw [ih b']
        simp

lemma restB_eq (f : List A → List B) (u : List (Option A)) :
    restB f u = midB f u ++ (if hasSep u then (f (sufBlk u)).map some else []) := by
  induction u with
  | nil => simp [midB]
  | cons x u ih =>
      cases x with
      | none =>
          rw [restB_cons_none, ih]
          cases hu : hasSep u with
          | false => simp [midB, hu, sufBlk, midB_eq_nil hu, sufBlk_eq_preBlk hu, hasSep]
          | true => simp [midB, hu, sufBlk, hasSep]
      | some a =>
          rw [restB_cons_some, ih]
          cases hu : hasSep u with
          | false => simp [midB, hu, hasSep]
          | true => simp [midB, hu, sufBlk, hasSep]

/-- **The decomposition of the image.**  The image of a string under the lifting of `f` is the
image of its first block, the middle, and the image of its last block. -/
lemma mapLift_eq_blocks (f : List A → List B) (u : List (Option A)) :
    mapLift f u = (f (preBlk u)).map some ++ midB f u ++
      (if hasSep u then (f (sufBlk u)).map some else []) := by
  rw [mapLift_eq_preBlk_restB, restB_eq, List.append_assoc]

/-! ## The compression of the image -/

/-- The two strings computed in the first pass over the given compression: the first and the last
block of the value of a rule. -/
def blkVal (rs : List (Rule (Option A))) (i : ℕ) (c : Bool) : List A :=
  if c then sufBlk (slpVal rs i) else preBlk (slpVal rs i)

/-- The string computed in the second pass over the given compression: the middle of the image of
the value of a rule. -/
def midVal (f : List A → List B) (rs : List (Rule (Option A))) (i : ℕ) (_ : Unit) :
    List (Option B) :=
  midB f (slpVal rs i)

private lemma mem_some_lt {ι : Type} {j i : ℕ} {c : ι} (h : j < i) :
    ∀ x ∈ some (j, c), x.1 < i := by
  intro x hx
  rw [Option.mem_def, Option.some_inj] at hx
  subst hx
  exact h

/-- The shape of the recursion required by the block construction, with a fixed string in the
middle and a reference to an earlier rule on each side. -/
private lemma blockRec_of_mid {ι B' : Type} {T : ℕ → ι → List B'} {i : ℕ} {c : ι} {K : ℕ}
    {p₁ p₂ : Option (ℕ × ι)} {ss : List (Rule B')} {t : List B'}
    (h₁ : ∀ x ∈ p₁, x.1 < i) (h₂ : ∀ x ∈ p₂, x.1 < i)
    (hss : Generates ss t) (hlen : ss.length + 2 ≤ K)
    (h : T i c = (p₁.elim [] fun x => T x.1 x.2) ++ t ++ (p₂.elim [] fun x => T x.1 x.2)) :
    ∃ (q₁ q₂ : Option (ℕ × ι)) (s₀ s₁ s₂ : List (Rule B')) (t₀ t₁ t₂ : List B'),
      (∀ x ∈ q₁, x.1 < i) ∧ (∀ x ∈ q₂, x.1 < i) ∧
      Generates s₀ t₀ ∧ Generates s₁ t₁ ∧ Generates s₂ t₂ ∧
      s₀.length + s₁.length + s₂.length ≤ K ∧
      T i c = t₀ ++ (q₁.elim [] fun x => T x.1 x.2) ++ t₁ ++
        (q₂.elim [] fun x => T x.1 x.2) ++ t₂ :=
  ⟨p₁, p₂, epsSLP, ss, epsSLP, [], t, [], h₁, h₂, generates_epsSLP, hss, generates_epsSLP,
    by simp only [length_epsSLP]; omega, by simpa using h⟩

/-- Every rule of a compression either has the empty value, or is a letter, or concatenates the
values of two earlier rules. -/
private lemma rule_cases {A' : Type} (rs : List (Rule A')) (i : ℕ) :
    slpVal rs i = [] ∨ (∃ x, rs[i]? = some (Rule.letter x)) ∨
      (∃ j k, rs[i]? = some (Rule.cat j k) ∧ j < i ∧ k < i) := by
  rcases hr : rs[i]? with _ | r
  · exact Or.inl (slpVal_of_getElem?_none hr)
  · cases r with
    | letter x => exact Or.inr (Or.inl ⟨x, rfl⟩)
    | cat j k =>
        by_cases hjk : j < i ∧ k < i
        · exact Or.inr (Or.inr ⟨j, k, rfl, hjk.1, hjk.2⟩)
        · exact Or.inl (slpVal_cat_bad hr hjk)

private lemma size_bound {C k n b1 b2 : ℕ} (hn : 1 ≤ n)
    (hb1 : b1 ≤ 1 + n * 20) (hb2 : b2 ≤ 1 + n * (C * (b1 + 2) ^ k + 10)) :
    2 * (C * (b1 + 1) ^ k) + (b2 + 1) + 2 ≤ (3 * C * 23 ^ k + 20) * n ^ (k + 1) := by
  have hm : 1 ≤ n ^ k := Nat.one_le_pow _ _ (by omega)
  have h23 : b1 + 2 ≤ 23 * n := by omega
  have h23' : b1 + 1 ≤ 23 * n := by omega
  have hX1 : (b1 + 1) ^ k ≤ 23 ^ k * n ^ k := by
    calc (b1 + 1) ^ k ≤ (23 * n) ^ k := Nat.pow_le_pow_left h23' k
      _ = 23 ^ k * n ^ k := Nat.mul_pow 23 n k
  have hX2 : (b1 + 2) ^ k ≤ 23 ^ k * n ^ k := by
    calc (b1 + 2) ^ k ≤ (23 * n) ^ k := Nat.pow_le_pow_left h23 k
      _ = 23 ^ k * n ^ k := Nat.mul_pow 23 n k
  have step1 : 2 * (C * (b1 + 1) ^ k) ≤ 2 * (C * (23 ^ k * n ^ k)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX1)
  have step2 : b2 ≤ 1 + n * (C * (23 ^ k * n ^ k) + 10) :=
    le_trans hb2 (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ hX2) _)) 1)
  have final : 2 * (C * (23 ^ k * n ^ k)) + ((1 + n * (C * (23 ^ k * n ^ k) + 10)) + 1) + 2
      ≤ (3 * C * 23 ^ k + 20) * n ^ (k + 1) := by
    have hY : (3 * C * 23 ^ k + 20) * n ^ (k + 1)
        = 3 * (n * (C * (23 ^ k * n ^ k))) + 20 * (n * n ^ k) := by
      rw [pow_succ]
      ring
    rw [hY]
    have h1 : C * (23 ^ k * n ^ k) ≤ n * (C * (23 ^ k * n ^ k)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h2 : n * (C * (23 ^ k * n ^ k) + 10) = n * (C * (23 ^ k * n ^ k)) + 10 * n := by ring
    have h3 : n ≤ n * n ^ k := Nat.le_mul_of_pos_right _ (by omega)
    omega
  exact le_trans (Nat.add_le_add (Nat.add_le_add step1 (Nat.add_le_add_right step2 1))
    (le_refl 2)) final

/-- **Claim `claim:map-compression`, size half.**  If the image of a compressed string under `f`
has a compression of polynomial size, then so does the image under the lifting of `f`. -/
theorem exists_slp_of_mapLift {f : List A → List B} {C k : ℕ}
    (hf : ∀ (rs : List (Rule A)) (w : List A), Generates rs w →
      ∃ rs' : List (Rule B), Generates rs' (f w) ∧ rs'.length ≤ C * rs.length ^ k) :
    ∀ (rs : List (Rule (Option A))) (w : List (Option A)), Generates rs w →
      ∃ rs' : List (Rule (Option B)), Generates rs' (mapLift f w) ∧
        rs'.length ≤ (3 * C * 23 ^ k + 20) * rs.length ^ (k + 1) := by
  classical
  intro rs w hw
  have hn : 1 ≤ rs.length := List.length_pos_iff.2 hw.1
  have hlast : slpVal rs (rs.length - 1) = w := hw.2
  -- ### The first pass: the first and the last block of the value of every rule
  have hrec₁ : ∀ i < rs.length, ∀ c : Bool, ∃ (p₁ p₂ : Option (ℕ × Bool))
      (s₀ s₁ s₂ : List (Rule A)) (t₀ t₁ t₂ : List A),
      (∀ x ∈ p₁, x.1 < i) ∧ (∀ x ∈ p₂, x.1 < i) ∧
      Generates s₀ t₀ ∧ Generates s₁ t₁ ∧ Generates s₂ t₂ ∧
      s₀.length + s₁.length + s₂.length ≤ 5 ∧
      blkVal rs i c = t₀ ++ (p₁.elim [] fun x => blkVal rs x.1 x.2) ++ t₁ ++
        (p₂.elim [] fun x => blkVal rs x.1 x.2) ++ t₂ := by
    intro i _ c
    rcases rule_cases rs i with hv | ⟨x, hr⟩ | ⟨j, k', hr, hj₀, hk₀⟩
    · refine blockRec_of_mid (T := blkVal rs) (i := i) (c := c) (p₁ := none) (p₂ := none)
        (by simp) (by simp) (generates_epsSLP (A := A)) (by simp) ?_
      cases c <;> simp [blkVal, hv]
    · refine blockRec_of_mid (T := blkVal rs) (i := i) (c := c) (p₁ := none) (p₂ := none)
        (by simp) (by simp) (generates_strSLP (blkVal rs i c)) ?_ (by simp)
      have h1 : (blkVal rs i c).length ≤ 1 := by
        rw [blkVal, slpVal_letter hr]
        cases x <;> cases c <;> simp [preBlk, sufBlk, hasSep]
      have h2 := length_strSLP (blkVal rs i c)
      omega
    · have hval : slpVal rs i = slpVal rs j ++ slpVal rs k' := slpVal_cat hr hj₀ hk₀
      cases c with
      | false =>
          by_cases hj : hasSep (slpVal rs j)
          · refine blockRec_of_mid (T := blkVal rs) (i := i) (c := false)
              (p₁ := some (j, false)) (p₂ := none) (mem_some_lt hj₀) (by simp)
              (generates_epsSLP (A := A)) (by simp) ?_
            simp [blkVal, hval, preBlk_append, hj]
          · refine blockRec_of_mid (T := blkVal rs) (i := i) (c := false)
              (p₁ := some (j, false)) (p₂ := some (k', false)) (mem_some_lt hj₀)
              (mem_some_lt hk₀) (generates_epsSLP (A := A)) (by simp) ?_
            simp [blkVal, hval, preBlk_append, hj]
      | true =>
          by_cases hk : hasSep (slpVal rs k')
          · refine blockRec_of_mid (T := blkVal rs) (i := i) (c := true)
              (p₁ := none) (p₂ := some (k', true)) (by simp) (mem_some_lt hk₀)
              (generates_epsSLP (A := A)) (by simp) ?_
            simp [blkVal, hval, sufBlk_append, hk]
          · refine blockRec_of_mid (T := blkVal rs) (i := i) (c := true)
              (p₁ := some (j, true)) (p₂ := some (k', true)) (mem_some_lt hj₀)
              (mem_some_lt hk₀) (generates_epsSLP (A := A)) (by simp) ?_
            simp [blkVal, hval, sufBlk_append, hk]
  obtain ⟨b₁, idx₁, pos₁, eps₁, len₁, hidx₁⟩ := exists_blockSLP (blkVal rs) rs.length 5 hrec₁
  have hb1 : b₁.length ≤ 1 + rs.length * 20 := by
    rw [show Fintype.card Bool = 2 from rfl] at len₁
    simpa using len₁
  -- ### The junction blocks
  have hjunc : ∀ j k' : ℕ, j < rs.length → k' < rs.length →
      ∃ ss : List (Rule (Option B)),
        Generates ss ((f (sufBlk (slpVal rs j) ++ preBlk (slpVal rs k'))).map some) ∧
        ss.length ≤ C * (b₁.length + 2) ^ k := by
    intro j k' hj hk'
    obtain ⟨ss₀, hss₀, hlen₀⟩ := exists_generates_cat_of_roots pos₁ eps₁
      (hidx₁ j hj true).1 (hidx₁ k' hk' false).1
    rw [(hidx₁ j hj true).2, (hidx₁ k' hk' false).2] at hss₀
    simp only [blkVal, if_true] at hss₀
    obtain ⟨ss₁, hss₁, hlen₁⟩ := hf ss₀ _ hss₀
    exact ⟨ss₁.map (mapRule some), generates_map hss₁,
      by rw [List.length_map, ← hlen₀]; exact hlen₁⟩
  -- ### The second pass: the middle of the image of the value of every rule
  have hrec₂ : ∀ i < rs.length, ∀ c : Unit, ∃ (p₁ p₂ : Option (ℕ × Unit))
      (s₀ s₁ s₂ : List (Rule (Option B))) (t₀ t₁ t₂ : List (Option B)),
      (∀ x ∈ p₁, x.1 < i) ∧ (∀ x ∈ p₂, x.1 < i) ∧
      Generates s₀ t₀ ∧ Generates s₁ t₁ ∧ Generates s₂ t₂ ∧
      s₀.length + s₁.length + s₂.length ≤ C * (b₁.length + 2) ^ k + 5 ∧
      midVal f rs i c = t₀ ++ (p₁.elim [] fun x => midVal f rs x.1 x.2) ++ t₁ ++
        (p₂.elim [] fun x => midVal f rs x.1 x.2) ++ t₂ := by
    intro i hi c
    rcases rule_cases rs i with hv | ⟨x, hr⟩ | ⟨j, k', hr, hj₀, hk₀⟩
    · refine blockRec_of_mid (T := midVal f rs) (i := i) (c := c) (p₁ := none) (p₂ := none)
        (by simp) (by simp) (generates_epsSLP (A := Option B)) (by simp) ?_
      simp [midVal, hv, midB]
    · refine blockRec_of_mid (T := midVal f rs) (i := i) (c := c) (p₁ := none) (p₂ := none)
        (by simp) (by simp) (generates_strSLP (midVal f rs i c)) ?_ (by simp)
      have h1 : (midVal f rs i c).length ≤ 1 := by
        rw [midVal, slpVal_letter hr]
        cases x <;> simp [midB, hasSep]
      have h2 := length_strSLP (midVal f rs i c)
      omega
    · have hval : slpVal rs i = slpVal rs j ++ slpVal rs k' := slpVal_cat hr hj₀ hk₀
      have hj' : j < rs.length := lt_of_lt_of_le hj₀ (le_of_lt hi)
      have hk' : k' < rs.length := lt_of_lt_of_le hk₀ (le_of_lt hi)
      by_cases hj : hasSep (slpVal rs j)
      · by_cases hk : hasSep (slpVal rs k')
        · obtain ⟨ss, hss, hsslen⟩ := hjunc j k' hj' hk'
          refine blockRec_of_mid (T := midVal f rs) (i := i) (c := c)
            (p₁ := some (j, ())) (p₂ := some (k', ())) (mem_some_lt hj₀)
            (mem_some_lt hk₀) hss (by omega) ?_
          simp [midVal, hval, midB_append, hj, hk]
        · refine blockRec_of_mid (T := midVal f rs) (i := i) (c := c)
            (p₁ := some (j, ())) (p₂ := none) (mem_some_lt hj₀) (by simp)
            (generates_epsSLP (A := Option B)) (by simp) ?_
          simp [midVal, hval, midB_append, hj, hk]
      · by_cases hk : hasSep (slpVal rs k')
        · refine blockRec_of_mid (T := midVal f rs) (i := i) (c := c)
            (p₁ := none) (p₂ := some (k', ())) (by simp) (mem_some_lt hk₀)
            (generates_epsSLP (A := Option B)) (by simp) ?_
          simp [midVal, hval, midB_append, hj, hk]
        · refine blockRec_of_mid (T := midVal f rs) (i := i) (c := c)
            (p₁ := none) (p₂ := none) (by simp) (by simp)
            (generates_epsSLP (A := Option B)) (by simp) ?_
          simp [midVal, hval, midB_append, hj, hk]
  obtain ⟨b₂, idx₂, pos₂, eps₂, len₂, hidx₂⟩ :=
    exists_blockSLP (midVal f rs) rs.length (C * (b₁.length + 2) ^ k + 5) hrec₂
  have hb2 : b₂.length ≤ 1 + rs.length * (C * (b₁.length + 2) ^ k + 10) := by
    rw [show Fintype.card Unit = 1 from rfl] at len₂
    have harg : 1 * (C * (b₁.length + 2) ^ k + 5 + 5) = C * (b₁.length + 2) ^ k + 10 := by ring
    rwa [harg] at len₂
  -- ### The three pieces of the image
  have hroot : ∀ c : Bool, ∃ ss : List (Rule (Option B)),
      Generates ss ((f (blkVal rs (rs.length - 1) c)).map some) ∧
      ss.length ≤ C * (b₁.length + 1) ^ k := by
    intro c
    obtain ⟨ss₀, hss₀, hlen₀⟩ := generates_of_buildSt
      (BuildSt.mk pos₁ eps₁ (hidx₁ (rs.length - 1) (by omega) c).1
        (hidx₁ (rs.length - 1) (by omega) c).2)
    obtain ⟨ss₁, hss₁, hlen₁⟩ := hf ss₀ _ hss₀
    exact ⟨ss₁.map (mapRule some), generates_map hss₁,
      by rw [List.length_map, ← hlen₀]; exact hlen₁⟩
  obtain ⟨sP, hsP, hsPlen⟩ := hroot false
  obtain ⟨sS, hsS, hsSlen⟩ := hroot true
  rw [blkVal, if_neg (by simp), hlast] at hsP
  rw [blkVal, if_pos rfl, hlast] at hsS
  obtain ⟨sM, hsM, hsMlen⟩ := generates_of_buildSt
    (BuildSt.mk pos₂ eps₂ (hidx₂ (rs.length - 1) (by omega) ()).1
      (hidx₂ (rs.length - 1) (by omega) ()).2)
  rw [midVal, hlast] at hsM
  -- ### Assembling them
  have hsize := size_bound (C := C) (k := k) (n := rs.length) (b1 := b₁.length)
    (b2 := b₂.length) hn hb1 hb2
  rw [mapLift_eq_blocks]
  by_cases hws : hasSep w
  · refine ⟨catSLP sP (catSLP sM sS), ?_, ?_⟩
    · rw [if_pos hws, List.append_assoc]
      exact generates_catSLP hsP (generates_catSLP hsM hsS)
    · rw [length_catSLP, length_catSLP]
      omega
  · refine ⟨sP, ?_, ?_⟩
    · rw [if_neg hws, midB_eq_nil (by simpa using hws)]
      simpa using hsP
    · omega

end Exercises
end Transducers
