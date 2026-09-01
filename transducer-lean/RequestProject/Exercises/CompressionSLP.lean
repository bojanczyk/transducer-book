/-
Combining grammar compressions.

The notion of a grammar compression is the one of `RequestProject/Exercises/Compression.lean`
(Exercise `exer:rational-compression`): a list of rules, the `i`-th of which is either a single
letter or the concatenation of the values of two *earlier* rules, the string generated being the
value of the last rule.

This file provides the operations on compressions that the solutions of Exercise
`exer:rational-compression` and Exercise `exer:regular-compression` build with: a compression can be
relocated inside a longer list of rules, two compressions can be concatenated, a fixed string has a
compression of linear size, and a list of compressions can be concatenated at the cost of one extra
rule per piece.
-/
import RequestProject.Exercises.Compression

namespace Transducers
namespace Exercises

variable {A : Type}

/-! ## Relocating a compression -/

/-- Shift the indices occurring in a rule by `n`. -/
def Rule.shift (n : ℕ) : Rule A → Rule A
  | Rule.letter a => Rule.letter a
  | Rule.cat j k => Rule.cat (j + n) (k + n)

/-- The value of a rule whose right-hand side is not made of earlier rules. -/
lemma slpVal_cat_bad {rs : List (Rule A)} {i j k : ℕ} (h : rs[i]? = some (Rule.cat j k))
    (hjk : ¬(j < i ∧ k < i)) : slpVal rs i = [] := by
  rw [slpVal, h]
  simp [hjk]

lemma slpVal_of_getElem?_none {rs : List (Rule A)} {i : ℕ} (h : rs[i]? = none) :
    slpVal rs i = [] := by
  rw [slpVal, h]

/-- The value of a rule of an initial segment does not change when rules are appended. -/
lemma slpVal_append_of_lt (rs ss : List (Rule A)) :
    ∀ i, i < rs.length → slpVal (rs ++ ss) i = slpVal rs i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hget : (rs ++ ss)[i]? = rs[i]? := List.getElem?_append_left hi
    rcases h : rs[i]? with _ | r
    · rw [slpVal_of_getElem?_none (hget.trans h), slpVal_of_getElem?_none h]
    · cases r with
      | letter a => rw [slpVal_letter (hget.trans h), slpVal_letter h]
      | cat j k =>
          by_cases hjk : j < i ∧ k < i
          · rw [slpVal_cat (hget.trans h) hjk.1 hjk.2, slpVal_cat h hjk.1 hjk.2,
              ih j hjk.1 (by omega), ih k hjk.2 (by omega)]
          · rw [slpVal_cat_bad (hget.trans h) hjk, slpVal_cat_bad h hjk]

/-- The value of a relocated rule is the value it had before the relocation. -/
lemma slpVal_append_shift (rs ss : List (Rule A)) :
    ∀ i, slpVal (rs ++ ss.map (Rule.shift rs.length)) (rs.length + i) = slpVal ss i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hget : (rs ++ ss.map (Rule.shift rs.length))[rs.length + i]? =
        (ss.map (Rule.shift rs.length))[i]? := by
      rw [List.getElem?_append_right (by omega)]
      congr 1
      omega
    rw [List.getElem?_map] at hget
    rcases h : ss[i]? with _ | r
    · rw [h] at hget
      rw [slpVal_of_getElem?_none (by simpa using hget), slpVal_of_getElem?_none h]
    · rw [h] at hget
      cases r with
      | letter a =>
          rw [slpVal_letter (by simpa [Rule.shift] using hget), slpVal_letter h]
      | cat j k =>
          have hget' : (rs ++ ss.map (Rule.shift rs.length))[rs.length + i]? =
              some (Rule.cat (j + rs.length) (k + rs.length)) := by
            simpa [Rule.shift] using hget
          by_cases hjk : j < i ∧ k < i
          · rw [slpVal_cat hget' (by omega) (by omega), slpVal_cat h hjk.1 hjk.2,
              show j + rs.length = rs.length + j by omega,
              show k + rs.length = rs.length + k by omega, ih j hjk.1, ih k hjk.2]
          · rw [slpVal_cat_bad hget' (by omega), slpVal_cat_bad h hjk]

/-! ## Concatenating two compressions -/

/-- The concatenation of two compressions: the rules of the first, the relocated rules of the
second, and one final rule concatenating their last rules. -/
def catSLP (rs ss : List (Rule A)) : List (Rule A) :=
  (rs ++ ss.map (Rule.shift rs.length)) ++ [Rule.cat (rs.length - 1) (rs.length + ss.length - 1)]

@[simp] lemma length_catSLP (rs ss : List (Rule A)) :
    (catSLP rs ss).length = rs.length + ss.length + 1 := by
  simp [catSLP]
  omega

lemma generates_catSLP {rs ss : List (Rule A)} {u v : List A}
    (h1 : Generates rs u) (h2 : Generates ss v) : Generates (catSLP rs ss) (u ++ v) := by
  obtain ⟨hr, hu⟩ := h1
  obtain ⟨hs, hv⟩ := h2
  have hrl : 0 < rs.length := List.length_pos_iff.2 hr
  have hsl : 0 < ss.length := List.length_pos_iff.2 hs
  refine ⟨by simp [catSLP], ?_⟩
  have hlen : (catSLP rs ss).length - 1 = rs.length + ss.length := by
    rw [length_catSLP]; omega
  have hget : (catSLP rs ss)[rs.length + ss.length]? =
      some (Rule.cat (rs.length - 1) (rs.length + ss.length - 1)) := by
    rw [catSLP, List.getElem?_append_right (by simp)]
    simp
  rw [hlen, slpVal_cat hget (by omega) (by omega)]
  have e1 : slpVal (catSLP rs ss) (rs.length - 1) = slpVal rs (rs.length - 1) := by
    rw [catSLP, slpVal_append_of_lt _ _ _ (by simp; omega),
      slpVal_append_of_lt _ _ _ (by omega)]
  have e2 : slpVal (catSLP rs ss) (rs.length + ss.length - 1) = slpVal ss (ss.length - 1) := by
    rw [catSLP, slpVal_append_of_lt _ _ _ (by simp; omega),
      show rs.length + ss.length - 1 = rs.length + (ss.length - 1) by omega,
      slpVal_append_shift]
  rw [e1, e2, hu, hv]

/-! ## Compressions of fixed strings -/

/-- A compression of the empty string.  The rule is ill-formed, which is exactly the convention
under which `slpVal` gives it the empty value. -/
def epsSLP : List (Rule A) := [Rule.cat 0 0]

lemma generates_epsSLP : Generates (epsSLP : List (Rule A)) [] := by
  refine ⟨by simp [epsSLP], ?_⟩
  show slpVal epsSLP 0 = []
  rw [slpVal]
  simp [epsSLP]

@[simp] lemma length_epsSLP : (epsSLP : List (Rule A)).length = 1 := rfl

/-- A compression of a fixed string: one rule per letter, concatenated from the left. -/
def strSLP : List A → List (Rule A)
  | [] => epsSLP
  | a :: u => catSLP [Rule.letter a] (strSLP u)

lemma generates_strSLP (u : List A) : Generates (strSLP u) u := by
  induction u with
  | nil => exact generates_epsSLP
  | cons a u ih =>
      have h1 : Generates [Rule.letter a] [a] := by
        refine ⟨by simp, ?_⟩
        exact slpVal_letter (by simp)
      exact generates_catSLP h1 ih

lemma length_strSLP (u : List A) : (strSLP u).length ≤ 2 * u.length + 1 := by
  induction u with
  | nil => simp [strSLP]
  | cons a u ih =>
      rw [strSLP, length_catSLP]
      simp only [List.length_cons, List.length_nil]
      omega

/-! ## Concatenating a list of compressions -/

/-- The concatenation of a list of compressions. -/
def catListSLP : List (List (Rule A)) → List (Rule A)
  | [] => epsSLP
  | rs :: l => catSLP rs (catListSLP l)

lemma generates_catListSLP {l : List (List (Rule A))} {us : List (List A)}
    (h : List.Forall₂ Generates l us) : Generates (catListSLP l) us.flatten := by
  induction h with
  | nil => simpa using (generates_epsSLP : Generates (epsSLP : List (Rule A)) [])
  | cons h₀ _ ih => simpa using generates_catSLP h₀ ih

lemma length_catListSLP :
    ∀ l : List (List (Rule A)),
      (catListSLP l).length ≤ (l.map List.length).sum + l.length + 1 := by
  intro l
  induction l with
  | nil => simp [catListSLP]
  | cons rs l ih =>
      rw [catListSLP, length_catSLP]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-! ## Building a compression block by block

The compressions built in the solution of Exercise `exer:regular-compression` all have the same
shape: the new compression has one *block* of rules for every rule of the given compression and
every element of a fixed finite index type, and the value of a block is obtained by concatenating
the values of at most two blocks of *earlier* rules with at most three fixed strings of bounded
compression size.  The theorem `exists_blockSLP` below performs that construction once and for all;
the number of rules it produces is linear in the number of rules of the given compression, with a
constant depending on the index type and on the bound for the fixed strings.
-/

section Block

variable {B ι : Type}

/-- `b'` extends `b`: the rules of `b'` are those of `b`, followed by others. -/
def Ext (b b' : List (Rule B)) : Prop := ∃ t, b' = b ++ t

lemma Ext.rfl' (b : List (Rule B)) : Ext b b := ⟨[], by simp⟩

lemma Ext.trans' {b b' b'' : List (Rule B)} (h : Ext b b') (h' : Ext b' b'') : Ext b b'' := by
  obtain ⟨t, rfl⟩ := h
  obtain ⟨t', rfl⟩ := h'
  exact ⟨t ++ t', by simp⟩

lemma Ext.length_le {b b' : List (Rule B)} (h : Ext b b') : b.length ≤ b'.length := by
  obtain ⟨t, rfl⟩ := h
  simp

lemma Ext.val_eq {b b' : List (Rule B)} (h : Ext b b') {i : ℕ} (hi : i < b.length) :
    slpVal b' i = slpVal b i := by
  obtain ⟨t, rfl⟩ := h
  exact slpVal_append_of_lt b t i hi

/-- Appending a rule that concatenates the values of two rules already present. -/
lemma exists_ext_cat (b : List (Rule B)) {r i : ℕ} (hr : r < b.length) (hi : i < b.length) :
    ∃ b' : List (Rule B), Ext b b' ∧ b'.length = b.length + 1 ∧
      slpVal b' b.length = slpVal b r ++ slpVal b i := by
  refine ⟨b ++ [Rule.cat r i], ⟨_, rfl⟩, by simp, ?_⟩
  have hget : (b ++ [Rule.cat r i])[b.length]? = some (Rule.cat r i) := by
    rw [List.getElem?_append_right (le_refl _)]
    simp
  rw [slpVal_cat hget hr hi, slpVal_append_of_lt b _ r hr, slpVal_append_of_lt b _ i hi]

/-- Appending a whole compression, relocated. -/
lemma exists_ext_graft (b : List (Rule B)) {ss : List (Rule B)} {u : List B} (h : Generates ss u) :
    ∃ (b' : List (Rule B)) (r : ℕ), Ext b b' ∧ b'.length = b.length + ss.length ∧
      r < b'.length ∧ slpVal b' r = u := by
  have hpos : 0 < ss.length := List.length_pos_iff.2 h.1
  refine ⟨b ++ ss.map (Rule.shift b.length), b.length + (ss.length - 1), ⟨_, rfl⟩, by simp,
    by simp only [List.length_append, List.length_map]; omega, ?_⟩
  rw [slpVal_append_shift b ss (ss.length - 1)]
  exact h.2

/-- The invariant maintained while a compression is built by blocks: the rule `0` has the empty
value, so that a missing piece can be supplied by referring to it, and the rule `r` has the value
`u` built so far. -/
structure BuildSt (b : List (Rule B)) (r : ℕ) (u : List B) : Prop where
  /-- There is at least one rule. -/
  pos : 0 < b.length
  /-- The first rule has the empty value. -/
  eps : slpVal b 0 = []
  /-- The current rule is present. -/
  lt : r < b.length
  /-- The value of the current rule. -/
  val : slpVal b r = u

lemma BuildSt.ext {b b' : List (Rule B)} {r : ℕ} {u : List B} (hg : BuildSt b r u)
    (h : Ext b b') : BuildSt b' r u :=
  ⟨lt_of_lt_of_le hg.pos h.length_le, by rw [h.val_eq hg.pos, hg.eps],
    lt_of_lt_of_le hg.lt h.length_le, by rw [h.val_eq hg.lt, hg.val]⟩

lemma BuildSt.append_ref {b : List (Rule B)} {r : ℕ} {u : List B} (hg : BuildSt b r u) {i : ℕ}
    (hi : i < b.length) :
    ∃ (b' : List (Rule B)) (r' : ℕ), Ext b b' ∧ b'.length = b.length + 1 ∧
      BuildSt b' r' (u ++ slpVal b i) := by
  obtain ⟨b', hext, hlen, hval⟩ := exists_ext_cat b hg.lt hi
  refine ⟨b', b.length, hext, hlen, ⟨by omega, ?_, by omega, ?_⟩⟩
  · rw [hext.val_eq hg.pos, hg.eps]
  · rw [hval, hg.val]

lemma BuildSt.append_lit {b : List (Rule B)} {r : ℕ} {u : List B} (hg : BuildSt b r u)
    {ss : List (Rule B)} {v : List B} (h : Generates ss v) :
    ∃ (b' : List (Rule B)) (r' : ℕ), Ext b b' ∧ b'.length ≤ b.length + ss.length + 1 ∧
      BuildSt b' r' (u ++ v) := by
  obtain ⟨b₁, r₁, hext₁, hlen₁, hlt₁, hval₁⟩ := exists_ext_graft b h
  obtain ⟨b₂, r₂, hext₂, hlen₂, hg₂⟩ := (hg.ext hext₁).append_ref hlt₁
  refine ⟨b₂, r₂, hext₁.trans' hext₂, by omega, ?_⟩
  rwa [hval₁] at hg₂

/-- A compression can be obtained from a rule of a partially built compression. -/
lemma generates_of_buildSt {b : List (Rule B)} {r : ℕ} {u : List B} (hg : BuildSt b r u) :
    ∃ ss : List (Rule B), Generates ss u ∧ ss.length = b.length + 1 := by
  refine ⟨b ++ [Rule.cat r 0], ⟨by simp, ?_⟩, by simp⟩
  have hget : (b ++ [Rule.cat r 0])[b.length]? = some (Rule.cat r 0) := by
    rw [List.getElem?_append_right (le_refl _)]
    simp
  have hlen : (b ++ [Rule.cat r 0]).length - 1 = b.length := by simp
  rw [hlen, slpVal_cat hget hg.lt hg.pos, slpVal_append_of_lt b _ r hg.lt,
    slpVal_append_of_lt b _ 0 hg.pos, hg.val, hg.eps, List.append_nil]

/-- One block: three fixed strings interleaved with the values of two rules already present. -/
lemma exists_ext_block {b : List (Rule B)} (hpos : 0 < b.length) (heps : slpVal b 0 = [])
    {s₀ s₁ s₂ : List (Rule B)} {t₀ t₁ t₂ : List B}
    (h₀ : Generates s₀ t₀) (h₁ : Generates s₁ t₁) (h₂ : Generates s₂ t₂)
    {i₁ i₂ : ℕ} (hi₁ : i₁ < b.length) (hi₂ : i₂ < b.length) :
    ∃ (b' : List (Rule B)) (r : ℕ), Ext b b' ∧
      b'.length ≤ b.length + (s₀.length + s₁.length + s₂.length + 5) ∧
      BuildSt b' r (t₀ ++ slpVal b i₁ ++ t₁ ++ slpVal b i₂ ++ t₂) := by
  have hg0 : BuildSt b 0 [] := ⟨hpos, heps, hpos, heps⟩
  obtain ⟨b₁, r₁, e₁, l₁, g₁⟩ := hg0.append_lit h₀
  obtain ⟨b₂, r₂, e₂, l₂, g₂⟩ := g₁.append_ref (lt_of_lt_of_le hi₁ e₁.length_le)
  rw [e₁.val_eq hi₁] at g₂
  obtain ⟨b₃, r₃, e₃, l₃, g₃⟩ := g₂.append_lit h₁
  obtain ⟨b₄, r₄, e₄, l₄, g₄⟩ := g₃.append_ref
    (lt_of_lt_of_le hi₂ (le_trans e₁.length_le (le_trans e₂.length_le e₃.length_le)))
  rw [(e₁.trans' (e₂.trans' e₃)).val_eq hi₂] at g₄
  obtain ⟨b₅, r₅, e₅, l₅, g₅⟩ := g₄.append_lit h₂
  refine ⟨b₅, r₅, e₁.trans' (e₂.trans' (e₃.trans' (e₄.trans' e₅))), by omega, ?_⟩
  have : ([] ++ t₀ ++ slpVal b i₁ ++ t₁ ++ slpVal b i₂ ++ t₂ : List B)
      = t₀ ++ slpVal b i₁ ++ t₁ ++ slpVal b i₂ ++ t₂ := by simp
  rwa [this] at g₅

/-- One row of blocks: a block for every element of a list of indices. -/
lemma exists_ext_row (l : List ι) {b : List (Rule B)} (hpos : 0 < b.length)
    (heps : slpVal b 0 = []) (V : ι → List B) (K : ℕ)
    (hrec : ∀ c : ι, ∃ (i₁ i₂ : ℕ) (s₀ s₁ s₂ : List (Rule B)) (t₀ t₁ t₂ : List B),
      i₁ < b.length ∧ i₂ < b.length ∧ Generates s₀ t₀ ∧ Generates s₁ t₁ ∧ Generates s₂ t₂ ∧
      s₀.length + s₁.length + s₂.length ≤ K ∧
      V c = t₀ ++ slpVal b i₁ ++ t₁ ++ slpVal b i₂ ++ t₂) :
    ∃ (b' : List (Rule B)) (g : ι → ℕ), Ext b b' ∧ b'.length ≤ b.length + l.length * (K + 5) ∧
      0 < b'.length ∧ slpVal b' 0 = [] ∧ ∀ c ∈ l, g c < b'.length ∧ slpVal b' (g c) = V c := by
  classical
  induction l with
  | nil => exact ⟨b, fun _ => 0, Ext.rfl' b, by simp, hpos, heps, by simp⟩
  | cons c l ih =>
      obtain ⟨b₁, g, e₁, len₁, pos₁, eps₁, hg⟩ := ih
      obtain ⟨i₁, i₂, s₀, s₁, s₂, t₀, t₁, t₂, hi₁, hi₂, h₀, h₁, h₂, hlen, hV⟩ := hrec c
      obtain ⟨b₂, r, e₂, len₂, gd⟩ := exists_ext_block pos₁ eps₁ h₀ h₁ h₂
        (lt_of_lt_of_le hi₁ e₁.length_le) (lt_of_lt_of_le hi₂ e₁.length_le)
      rw [e₁.val_eq hi₁, e₁.val_eq hi₂, ← hV] at gd
      refine ⟨b₂, fun d => if d = c then r else g d, e₁.trans' e₂, ?_, gd.pos, gd.eps, ?_⟩
      · simp only [List.length_cons]
        have : (l.length + 1) * (K + 5) = l.length * (K + 5) + (K + 5) := by ring
        omega
      · intro d hd
        by_cases hdc : d = c
        · subst hdc
          have hif : (if d = d then r else g d) = r := if_pos rfl
          show (if d = d then r else g d) < b₂.length ∧
            slpVal b₂ (if d = d then r else g d) = V d
          rw [hif]
          exact ⟨gd.lt, gd.val⟩
        · show (if d = c then r else g d) < b₂.length ∧
            slpVal b₂ (if d = c then r else g d) = V d
          simp only [if_neg hdc]
          have hdl : d ∈ l := by
            rcases List.mem_cons.1 hd with h | h
            · exact absurd h hdc
            · exact h
          obtain ⟨h1, h2⟩ := hg d hdl
          exact ⟨lt_of_lt_of_le h1 e₂.length_le, by rw [e₂.val_eq h1, h2]⟩

/-- **The block construction.**  Suppose that for every `i < n` and every index `c` the string
`T i c` is the concatenation of at most three strings with compressions of at most `K` rules in
total and of at most two strings `T j d` with `j < i`.  Then all the strings `T i c` are the values
of the rules of a single compression with `O(n)` rules. -/
theorem exists_blockSLP [Fintype ι] (T : ℕ → ι → List B) (n K : ℕ)
    (hrec : ∀ i < n, ∀ c : ι, ∃ (p₁ p₂ : Option (ℕ × ι)) (s₀ s₁ s₂ : List (Rule B))
        (t₀ t₁ t₂ : List B),
      (∀ x ∈ p₁, x.1 < i) ∧ (∀ x ∈ p₂, x.1 < i) ∧
      Generates s₀ t₀ ∧ Generates s₁ t₁ ∧ Generates s₂ t₂ ∧
      s₀.length + s₁.length + s₂.length ≤ K ∧
      T i c = t₀ ++ (p₁.elim [] fun x => T x.1 x.2) ++ t₁ ++
        (p₂.elim [] fun x => T x.1 x.2) ++ t₂) :
    ∃ (b : List (Rule B)) (idx : ℕ → ι → ℕ), 0 < b.length ∧ slpVal b 0 = [] ∧
      b.length ≤ 1 + n * (Fintype.card ι * (K + 5)) ∧
      ∀ i < n, ∀ c : ι, idx i c < b.length ∧ slpVal b (idx i c) = T i c := by
  classical
  induction n with
  | zero =>
      refine ⟨epsSLP, fun _ _ => 0, by simp, ?_, by simp, by omega⟩
      have := generates_epsSLP (A := B)
      simpa using this.2
  | succ N ih =>
      obtain ⟨b, idx, hpos, heps, hlen, hidx⟩ := ih (fun i hi => hrec i (by omega))
      have hrow : ∀ c : ι, ∃ (i₁ i₂ : ℕ) (s₀ s₁ s₂ : List (Rule B)) (t₀ t₁ t₂ : List B),
          i₁ < b.length ∧ i₂ < b.length ∧ Generates s₀ t₀ ∧ Generates s₁ t₁ ∧ Generates s₂ t₂ ∧
          s₀.length + s₁.length + s₂.length ≤ K ∧
          T N c = t₀ ++ slpVal b i₁ ++ t₁ ++ slpVal b i₂ ++ t₂ := by
        intro c
        obtain ⟨p₁, p₂, s₀, s₁, s₂, t₀, t₁, t₂, hp₁, hp₂, h₀, h₁, h₂, hK, hT⟩ :=
          hrec N (by omega) c
        have key : ∀ p : Option (ℕ × ι), (∀ x ∈ p, x.1 < N) →
            ∃ i : ℕ, i < b.length ∧ slpVal b i = p.elim [] fun x => T x.1 x.2 := by
          intro p hp
          rcases p with _ | x
          · exact ⟨0, hpos, heps⟩
          · exact ⟨idx x.1 x.2, (hidx x.1 (hp x rfl) x.2).1, (hidx x.1 (hp x rfl) x.2).2⟩
        obtain ⟨i₁, hi₁, hv₁⟩ := key p₁ hp₁
        obtain ⟨i₂, hi₂, hv₂⟩ := key p₂ hp₂
        exact ⟨i₁, i₂, s₀, s₁, s₂, t₀, t₁, t₂, hi₁, hi₂, h₀, h₁, h₂, hK, by rw [hT, hv₁, hv₂]⟩
      obtain ⟨b', g, e, len', pos', eps', hg⟩ :=
        exists_ext_row (Finset.univ : Finset ι).toList hpos heps (fun c => T N c) K hrow
      refine ⟨b', fun i c => if i = N then g c else idx i c, pos', eps', ?_, ?_⟩
      · have hl : (Finset.univ : Finset ι).toList.length = Fintype.card ι := by
            simp [Finset.length_toList]
        rw [hl] at len'
        have : (N + 1) * (Fintype.card ι * (K + 5))
            = N * (Fintype.card ι * (K + 5)) + Fintype.card ι * (K + 5) := by ring
        omega
      · intro i hi c
        by_cases hiN : i = N
        · subst hiN
          have hif : (if i = i then g c else idx i c) = g c := if_pos rfl
          show (if i = i then g c else idx i c) < b'.length ∧
            slpVal b' (if i = i then g c else idx i c) = T i c
          rw [hif]
          exact hg c (by simp)
        · show (if i = N then g c else idx i c) < b'.length ∧
            slpVal b' (if i = N then g c else idx i c) = T i c
          simp only [if_neg hiN]
          obtain ⟨h1, h2⟩ := hidx i (by omega) c
          exact ⟨lt_of_lt_of_le h1 e.length_le, by rw [e.val_eq h1, h2]⟩

/-- The concatenation of the values of two rules of a partially built compression is generated by a
compression with two more rules. -/
lemma exists_generates_cat_of_roots {b : List (Rule B)} (hpos : 0 < b.length)
    (heps : slpVal b 0 = []) {i j : ℕ} (hi : i < b.length) (hj : j < b.length) :
    ∃ ss : List (Rule B), Generates ss (slpVal b i ++ slpVal b j) ∧ ss.length = b.length + 2 := by
  obtain ⟨b', hext, hlen, hval⟩ := exists_ext_cat b hi hj
  have hb' : BuildSt b' b.length (slpVal b i ++ slpVal b j) :=
    ⟨by omega, by rw [hext.val_eq hpos, heps], by omega, hval⟩
  obtain ⟨ss, hss, hsslen⟩ := generates_of_buildSt hb'
  exact ⟨ss, hss, by omega⟩

end Block

/-! ## Renaming the letters of a compression -/

variable {B : Type}

/-- Renaming the letters of a compression. -/
def mapRule (h : A → B) : Rule A → Rule B
  | Rule.letter a => Rule.letter (h a)
  | Rule.cat j k => Rule.cat j k

lemma slpVal_map (h : A → B) (rs : List (Rule A)) :
    ∀ i, slpVal (rs.map (mapRule h)) i = (slpVal rs i).map h := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hget : (rs.map (mapRule h))[i]? = (rs[i]?).map (mapRule h) := List.getElem?_map ..
    rcases hr : rs[i]? with _ | r
    · rw [hr] at hget
      rw [slpVal_of_getElem?_none (by simpa using hget), slpVal_of_getElem?_none hr]
      rfl
    · rw [hr] at hget
      cases r with
      | letter a =>
          rw [slpVal_letter (by simpa [mapRule] using hget), slpVal_letter hr]
          rfl
      | cat j k =>
          have hget' : (rs.map (mapRule h))[i]? = some (Rule.cat j k) := by
            simpa [mapRule] using hget
          by_cases hjk : j < i ∧ k < i
          · rw [slpVal_cat hget' hjk.1 hjk.2, slpVal_cat hr hjk.1 hjk.2, ih j hjk.1, ih k hjk.2,
              List.map_append]
          · rw [slpVal_cat_bad hget' hjk, slpVal_cat_bad hr hjk]
            rfl

lemma generates_map {h : A → B} {rs : List (Rule A)} {u : List A} (hu : Generates rs u) :
    Generates (rs.map (mapRule h)) (u.map h) := by
  refine ⟨by simpa using hu.1, ?_⟩
  rw [List.length_map, slpVal_map, hu.2]

end Exercises
end Transducers
