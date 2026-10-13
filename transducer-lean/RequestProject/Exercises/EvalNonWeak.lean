/-
Exercise `exer:non-weak-simon-tree-not-aperiodic` of Part D, Section *Evaluation*
(`partDPolyregular/evaluation.tex`), the combinatorial core: no Simon tree, for the monoid
`{0, 1, 2}` of addition capped at `2`, has a bracket encoding containing a factor
`a R a R a`, where `a` is a leaf and `R` is a word of brackets with as many opening as closing
brackets.

The book's argument considers positions that are paired with their successor by a subtree with two
leaves.  The argument used here works directly on the encoding of the tree.  Call `x₁ < x₂ < x₃`
the positions of the three leaves of the factor `a R a R a`; since `R` is balanced, the
bracket depth of the encoding is the same at a position `j` with `x₁ < j ≤ x₂` and at `j + |R| + 1`.
A node whose encoding starts strictly between `x₁` and `x₂` (or ends strictly between `x₂` and `x₃`)
therefore closes (or opens) within `|R| + 1` symbols, and contains at most the leaf `x₂`.  Now take
the child, containing `x₂`, of a node that contains all three leaves: if it does not itself contain
the three leaves, then it contains `x₂` only, its label is `1`, which is not idempotent, so the node
has at most two children -- but `x₁` and `x₃` lie in children on both sides of it.  Descending, this
is a contradiction.

`PartD`'s bracket encoding `Transducers.FactTree.enc` (`PartD/SimonRat.lean`) is used.
-/
import RequestProject.PartD.SimonRat

namespace Transducers.Exercises

open FactTree TreeSym

/-! ## The monoid `({0, 1, 2}, capped addition)` -/

/-- The monoid `{0, 1, 2}` with addition capped at `2`. -/
def Cap2 : Type := Fin 3

namespace Cap2

instance : Fintype Cap2 := inferInstanceAs (Fintype (Fin 3))

instance : DecidableEq Cap2 := inferInstanceAs (DecidableEq (Fin 3))

/-- The underlying number of an element of `Cap2`. -/
def val (x : Cap2) : ℕ := Fin.val (n := 3) x

lemma val_lt (x : Cap2) : x.val < 3 := Fin.isLt (n := 3) x

lemma ext {x y : Cap2} (h : x.val = y.val) : x = y := Fin.ext (n := 3) h

/-- An element of `Cap2` from a number below `3`. -/
def mk (n : ℕ) (h : n < 3) : Cap2 := (⟨n, h⟩ : Fin 3)

@[simp] lemma val_mk (n : ℕ) (h : n < 3) : (mk n h).val = n := rfl

instance : CommMonoid Cap2 where
  mul a b := mk (min (a.val + b.val) 2) (by omega)
  one := mk 0 (by omega)
  mul_assoc a b c := ext (show min (min (a.val + b.val) 2 + c.val) 2 =
    min (a.val + min (b.val + c.val) 2) 2 by omega)
  one_mul a := ext (show min (0 + a.val) 2 = a.val by have := a.val_lt; omega)
  mul_one a := ext (show min (a.val + 0) 2 = a.val by have := a.val_lt; omega)
  mul_comm a b := ext (show min (a.val + b.val) 2 = min (b.val + a.val) 2 by omega)

lemma val_mul (a b : Cap2) : (a * b).val = min (a.val + b.val) 2 := rfl

/-- The element `1` of `{0, 1, 2}` (not the identity of the monoid, which is `0`). -/
def one' : Cap2 := mk 1 (by omega)

lemma one'_not_idempotent : ¬ IsIdempotentElem one' := by
  intro h
  have := congrArg val h
  rw [val_mul] at this
  simp [one'] at this

/-- The monoid is aperiodic: `x³ = x²` for every element. -/
theorem aperiodic (x : Cap2) : x ^ 3 = x ^ 2 := by
  apply ext
  simp only [pow_succ, pow_zero, val_mul]
  have := x.val_lt
  change min (min (min (0 + x.val) 2 + x.val) 2 + x.val) 2 = min (min (0 + x.val) 2 + x.val) 2
  omega

end Cap2

/-- The homomorphism `{a}* → {0, 1, 2}` that maps a string to its length capped at `2`. -/
def capHom : FreeMonoid Unit →* Cap2 := FreeMonoid.lift fun _ => Cap2.one'

lemma capHom_single : capHom (FreeMonoid.ofList [()]) = Cap2.one' := by
  simp [capHom]

/-! ## Balance and number of letters of a word over the bracket alphabet -/

section Counts

variable {A : Type}

/-- The contribution of a symbol to the bracket depth. -/
def symBal : TreeSym A → ℤ
  | .op => 1
  | .cl => -1
  | .letter _ => 0

/-- `1` for a letter, `0` for a bracket. -/
def symLet : TreeSym A → ℕ
  | .letter _ => 1
  | _ => 0

/-- The number of opening minus the number of closing brackets. -/
def bal (u : List (TreeSym A)) : ℤ := (u.map symBal).sum

/-- The number of letters. -/
def lets (u : List (TreeSym A)) : ℕ := (u.map symLet).sum

@[simp] lemma bal_nil : bal ([] : List (TreeSym A)) = 0 := rfl
@[simp] lemma bal_cons (x : TreeSym A) (u : List (TreeSym A)) :
    bal (x :: u) = symBal x + bal u := by simp [bal]
@[simp] lemma bal_append (u v : List (TreeSym A)) : bal (u ++ v) = bal u + bal v := by
  simp [bal]
@[simp] lemma lets_nil : lets ([] : List (TreeSym A)) = 0 := rfl
@[simp] lemma lets_cons (x : TreeSym A) (u : List (TreeSym A)) :
    lets (x :: u) = symLet x + lets u := by simp [lets]
@[simp] lemma lets_append (u v : List (TreeSym A)) : lets (u ++ v) = lets u + lets v := by
  simp [lets]

lemma lets_flatten (L : List (List (TreeSym A))) : lets L.flatten = (L.map lets).sum := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [ih]

lemma bal_flatten (L : List (List (TreeSym A))) : bal L.flatten = (L.map bal).sum := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [ih]

lemma lets_take_le (u : List (TreeSym A)) {i j : ℕ} (hij : i ≤ j) :
    lets (u.take i) ≤ lets (u.take j) := by
  have : u.take j = u.take i ++ (u.drop i).take (j - i) := by
    rw [← List.take_add, Nat.add_sub_cancel' hij]
  rw [this, lets_append]
  omega

theorem enc_lets : ∀ t : FactTree A, lets t.enc = t.yield.length
  | leaf a => by simp [symLet]
  | node cs => by
    rw [enc_node, yield_node, lets_append, lets_append, lets_flatten, List.length_flatten,
      List.map_map, List.map_map]
    have : ∀ c ∈ cs, (lets ∘ enc) c = (List.length ∘ yield) c := fun c hc => by
      have := List.sizeOf_lt_of_mem hc
      exact enc_lets c
    rw [List.map_congr_left this]
    simp [symLet]

theorem enc_bal : ∀ t : FactTree A, bal t.enc = 0
  | leaf a => by simp [symBal]
  | node cs => by
    rw [enc_node, bal_append, bal_append, bal_flatten, List.map_map]
    have : ∀ c ∈ cs, (bal ∘ enc) c = 0 := fun c hc => by
      have := List.sizeOf_lt_of_mem hc
      exact enc_bal c
    rw [List.map_congr_left this]
    simp [symBal]

lemma flatten_take_bal_nonneg (L : List (List (TreeSym A)))
    (hL : ∀ l ∈ L, ∀ j, 0 ≤ bal (l.take j)) : ∀ j, 0 ≤ bal (L.flatten.take j) := by
  induction L with
  | nil => intro j; simp
  | cons l L ih =>
    intro j
    rw [List.flatten_cons, List.take_append, bal_append]
    have h1 := hL l List.mem_cons_self j
    have h2 := ih (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')) (j - l.length)
    omega

lemma bal_take_node (F : List (TreeSym A)) (j : ℕ) :
    bal (([TreeSym.op] ++ F ++ [TreeSym.cl]).take (j + 1)) =
      1 + bal (F.take j) + (if F.length < j then -1 else 0) := by
  simp only [List.singleton_append, List.take_succ_cons, bal_cons, symBal,
    List.take_append, bal_append, List.length_cons]
  split_ifs with h
  · rw [show j + 1 - (F.length + 1) = (j - F.length - 1) + 1 by omega]
    simp [symBal]
  · rw [show j + 1 - (F.length + 1) = 0 by omega]
    simp

theorem enc_take_bal_nonneg : ∀ (t : FactTree A) (j : ℕ), 0 ≤ bal (t.enc.take j)
  | leaf a, j => by
    rcases j with _ | j <;> simp [symBal]
  | node cs, j => by
    have hF : ∀ k, 0 ≤ bal ((cs.map enc).flatten.take k) := by
      apply flatten_take_bal_nonneg
      intro l hl
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
      have := List.sizeOf_lt_of_mem hc
      exact enc_take_bal_nonneg c
    have hF0 : bal (cs.map enc).flatten = 0 := by
      rw [bal_flatten, List.map_map]
      have : ∀ c ∈ cs, (bal ∘ enc) c = 0 := fun c _ => enc_bal c
      rw [List.map_congr_left this]
      simp
    rw [enc_node]
    rcases j with _ | j
    · simp
    · rw [bal_take_node]
      split_ifs with h
      · rw [List.take_of_length_le h.le, hF0]; omega
      · have := hF j; omega

theorem node_enc_take_bal_pos (cs : List (FactTree A)) (j : ℕ) (hj0 : 0 < j)
    (hj : j < (node cs).enc.length) : 1 ≤ bal ((node cs).enc.take j) := by
  have hF : ∀ k, 0 ≤ bal ((cs.map enc).flatten.take k) := by
    apply flatten_take_bal_nonneg
    intro l hl
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hl
    exact enc_take_bal_nonneg c
  simp only [enc_node, List.length_append, List.length_singleton] at hj
  rw [enc_node]
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [bal_take_node, if_neg (by omega)]
  have := hF j
  omega

end Counts

/-! ## Subtrees placed in a word -/

section Occ

variable {A : Type} (W : List (TreeSym A))

/-- `Occ W t s`: the encoding of `t` is the factor of `W` that starts at position `s`. -/
def Occ (t : FactTree A) (s : ℕ) : Prop :=
  ∃ P Q : List (TreeSym A), W = P ++ t.enc ++ Q ∧ P.length = s

/-- The bracket depth of `W` before position `i`. -/
def depthAt (i : ℕ) : ℤ := bal (W.take i)

/-- The number of letters of `W` before position `i`. -/
def letsAt (i : ℕ) : ℕ := lets (W.take i)

variable {W}

lemma letsAt_mono {i j : ℕ} (h : i ≤ j) : letsAt W i ≤ letsAt W j := lets_take_le W h

lemma Occ.take {t : FactTree A} {s : ℕ} (ht : Occ W t s) {j : ℕ} (hj : j ≤ t.enc.length) :
    W.take (s + j) = W.take s ++ t.enc.take j := by
  obtain ⟨P, Q, rfl, rfl⟩ := ht
  rw [List.append_assoc, List.take_length_add_append, List.take_left' rfl,
    List.take_append_of_le_length hj]

lemma Occ.letsAt_end {t : FactTree A} {s : ℕ} (ht : Occ W t s) :
    letsAt W (s + t.enc.length) = letsAt W s + t.yield.length := by
  rw [letsAt, ht.take le_rfl, List.take_length, lets_append, enc_lets]
  rfl

lemma Occ.depthAt_node {cs : List (FactTree A)} {s : ℕ} (ht : Occ W (node cs) s) {j : ℕ}
    (hj0 : 0 < j) (hj : j < (node cs).enc.length) : depthAt W s + 1 ≤ depthAt W (s + j) := by
  rw [depthAt, depthAt, ht.take hj.le, bal_append]
  have := node_enc_take_bal_pos cs j hj0 hj
  omega

lemma Occ.depthAt_end {t : FactTree A} {s : ℕ} (ht : Occ W t s) :
    depthAt W (s + t.enc.length) = depthAt W s := by
  rw [depthAt, depthAt, ht.take le_rfl, List.take_length, bal_append, enc_bal, add_zero]

lemma Occ.getElem_start {cs : List (FactTree A)} {s : ℕ} (ht : Occ W (node cs) s) :
    W[s]? = some TreeSym.op := by
  obtain ⟨P, Q, rfl, rfl⟩ := ht
  rw [enc_node]
  simp

lemma Occ.getElem_last {cs : List (FactTree A)} {s : ℕ} (ht : Occ W (node cs) s) :
    W[s + (node cs).enc.length - 1]? = some TreeSym.cl := by
  obtain ⟨P, Q, rfl, rfl⟩ := ht
  rw [enc_node]
  simp only [List.length_append, List.length_singleton]
  rw [show P.length + (1 + ((cs.map enc).flatten.length) + 1) - 1 =
    (P ++ ([TreeSym.op] ++ (cs.map enc).flatten)).length by simp; omega]
  simp

/-- The offset, inside the encoding of `node cs` and after its opening bracket, of the `i`-th
child. -/
def childOff (cs : List (FactTree A)) (i : ℕ) : ℕ := ((cs.take i).map fun c => c.enc.length).sum

lemma childOff_succ (cs : List (FactTree A)) (i : ℕ) (hi : i < cs.length) :
    childOff cs (i + 1) = childOff cs i + cs[i].enc.length := by
  rw [childOff, childOff, List.take_add_one, List.map_append, List.sum_append,
    List.getElem?_eq_getElem hi]
  simp

lemma childOff_length (cs : List (FactTree A)) :
    (node cs).enc.length = childOff cs cs.length + 2 := by
  rw [enc_node, childOff, List.take_length]
  simp [List.length_flatten, List.map_map, Function.comp_def]

lemma Occ.child {cs : List (FactTree A)} {s : ℕ} (ht : Occ W (node cs) s) (i : ℕ)
    (hi : i < cs.length) : Occ W cs[i] (s + 1 + childOff cs i) := by
  obtain ⟨P, Q, rfl, rfl⟩ := ht
  have hcs : cs = cs.take i ++ cs[i] :: cs.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  set l₁ := cs.take i
  set c := cs[i]
  set l₂ := cs.drop (i + 1)
  have hF : (cs.map enc).flatten = (l₁.map enc).flatten ++ c.enc ++ (l₂.map enc).flatten := by
    rw [hcs]; simp
  refine ⟨P ++ [TreeSym.op] ++ (l₁.map enc).flatten,
    (l₂.map enc).flatten ++ [TreeSym.cl] ++ Q, ?_, ?_⟩
  · rw [enc_node, hF]
    simp
  · simp [childOff, l₁, List.length_flatten, List.map_map, Function.comp_def]
    omega

end Occ

/-! ## The core argument -/

lemma exists_index_between (a : ℕ → ℕ) (x : ℕ) :
    ∀ k : ℕ, a 0 ≤ x → x < a k → ∃ i < k, a i ≤ x ∧ x < a (i + 1)
  | 0, h0, hk => absurd hk (by omega)
  | k + 1, h0, hk => by
    by_cases hx : x < a k
    · obtain ⟨i, hi, h1, h2⟩ := exists_index_between a x k h0 hx
      exact ⟨i, by omega, h1, h2⟩
    · exact ⟨k, by omega, by omega, hk⟩

/-- The hypotheses on the word `W` and the three positions `x₁ < x₂ < x₃` of letters, `d` apart, used
in the core argument: the bracket depth is `d`-periodic between `x₁` and `x₃`, and `x₂` is the only
letter strictly between `x₁` and `x₃`. -/
structure Window (W : List (TreeSym Unit)) (x₁ d : ℕ) : Prop where
  d_pos : 0 < d
  letter₁ : W[x₁]? = some (TreeSym.letter ())
  letter₃ : W[x₁ + d + d]? = some (TreeSym.letter ())
  lets₁ : letsAt W (x₁ + 1) = letsAt W x₁ + 1
  lets₂ : letsAt W (x₁ + d + 1) = letsAt W (x₁ + d) + 1
  lets₃ : letsAt W (x₁ + d + d + 1) = letsAt W (x₁ + d + d) + 1
  lets_mid : letsAt W (x₁ + d + d) ≤ letsAt W (x₁ + 1) + 1
  periodic : ∀ j, x₁ < j → j ≤ x₁ + d → depthAt W (j + d) = depthAt W j

/-- **The core argument.**  No Simon subtree for `capHom` placed in `W` contains the three letters
`x₁`, `x₁ + d`, `x₁ + 2d` of a window. -/
theorem no_simon_over_window {W : List (TreeSym Unit)} {x₁ d : ℕ} (hW : Window W x₁ d) :
    ∀ t : FactTree Unit, t.IsSimon capHom → ∀ s, Occ W t s → s ≤ x₁ →
      x₁ + d + d < s + t.enc.length → False := by
  intro t ht
  induction ht with
  | leaf a =>
    intro s _ h1 h2
    simp at h2
    have := hW.d_pos
    omega
  | node cs hcs hidem ih =>
    intro s hocc hs he
    have hd := hW.d_pos
    obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ, ∀ i, a i = s + 1 + childOff cs i := ⟨_, fun _ => rfl⟩
    have hlen := childOff_length cs
    have ha0 : a 0 = s + 1 := by rw [ha]; simp [childOff]
    have hak : a cs.length + 1 = s + (node cs).enc.length := by rw [ha, hlen]; omega
    -- the node starts before `x₁` and ends after `x₁ + 2d`
    have hs' : s < x₁ := by
      rcases Nat.lt_or_eq_of_le hs with h | h
      · exact h
      · have h1 := hocc.getElem_start
        rw [h, hW.letter₁] at h1
        simp at h1
    have he' : x₁ + d + d < a cs.length := by
      have h1 := hocc.getElem_last
      have : x₁ + d + d ≠ s + (node cs).enc.length - 1 := by
        intro h
        rw [← h, hW.letter₃] at h1
        simp at h1
      omega
    obtain ⟨i, hik, hai, hai1⟩ := exists_index_between a (x₁ + d) cs.length (by omega)
      (by omega)
    have hc := hocc.child i hik
    rw [← ha i] at hc
    have hci : a (i + 1) = a i + cs[i].enc.length := by
      rw [ha, ha, childOff_succ cs i hik]; omega
    have hcl := hc.letsAt_end
    rw [← hci] at hcl
    -- the child `cs[i]` either contains the three letters ...
    by_cases hA : a i ≤ x₁ ∧ x₁ + d + d < a (i + 1)
    · exact ih cs[i] (List.getElem_mem hik) (a i) hc hA.1 (by rw [← hci]; exact hA.2)
    -- ... or it contains exactly one letter, `x₁ + d`
    have hge : 1 ≤ cs[i].yield.length := by
      have h1 := letsAt_mono (W := W) (show x₁ + d + 1 ≤ a (i + 1) by omega)
      have h2 := letsAt_mono (W := W) hai
      have := hW.lets₂
      omega
    have hle : cs[i].yield.length ≤ 1 := by
      by_contra h2
      push_neg at h2
      obtain ⟨ds, hds⟩ : ∃ ds, cs[i] = node ds := by
        rcases hci' : cs[i] with b | ds
        · rw [hci'] at h2; simp at h2
        · exact ⟨ds, rfl⟩
      rw [hds] at hc hci hcl h2
      rcases Nat.lt_or_ge x₁ (a i) with h3 | h3
      · -- the child starts strictly between `x₁` and `x₁ + d`: it ends within `d` symbols
        have hper := hW.periodic (a i) h3 hai
        have hend : a (i + 1) ≤ a i + d := by
          by_contra h4
          have := hc.depthAt_node (j := d) hd (by omega)
          omega
        have h5 := letsAt_mono (W := W) (show a (i + 1) ≤ x₁ + d + d by omega)
        have h6 := letsAt_mono (W := W) (show x₁ + 1 ≤ a i by omega)
        have := hW.lets_mid
        omega
      · -- the child starts before `x₁`, so it ends strictly between `x₁ + d` and `x₁ + 2d`
        have h4 : a (i + 1) ≤ x₁ + d + d := by
          by_contra h4
          exact hA ⟨h3, by omega⟩
        have hper := hW.periodic (a (i + 1) - d) (by omega) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at hper
        have h5 := hc.depthAt_node (j := a (i + 1) - d - a i) (by omega) (by omega)
        have h6 := hc.depthAt_end
        rw [show a i + (a (i + 1) - d - a i) = a (i + 1) - d by omega] at h5
        rw [← hci] at h6
        omega
    have hy : cs[i].yield = [()] := by
      match h : cs[i].yield with
      | [u] => rfl
      | [] => rw [h] at hge; simp at hge
      | _ :: _ :: _ => rw [h] at hle; simp at hle
    -- so the label of `cs[i]` is not idempotent, and the node has at most two children
    have hk2 : cs.length ≤ 2 := by
      by_contra h3
      obtain ⟨e, he, hlab⟩ := hidem (by omega)
      have := hlab cs[i] (List.getElem_mem hik)
      rw [label, hy, capHom_single] at this
      exact Cap2.one'_not_idempotent (this ▸ he)
    -- but the letters `x₁` and `x₁ + 2d` lie in children on both sides of `cs[i]`
    have hone : letsAt W (a (i + 1)) = letsAt W (a i) + 1 := by
      rw [hcl, hy]; rfl
    have hi0 : 1 ≤ i := by
      by_contra h3
      have hi : i = 0 := by omega
      have h4 : a i ≤ x₁ := by rw [hi, ha0]; omega
      have h5 := letsAt_mono (W := W) h4
      have h6 := letsAt_mono (W := W) (show x₁ + 1 ≤ x₁ + d by omega)
      have h7 := letsAt_mono (W := W) (show x₁ + d + 1 ≤ a (i + 1) by omega)
      have := hW.lets₁
      have := hW.lets₂
      omega
    have hi1 : i + 2 ≤ cs.length := by
      by_contra h3
      have hi : i + 1 = cs.length := by omega
      have h4 : x₁ + d + d + 1 ≤ a (i + 1) := by rw [hi]; omega
      have h5 := letsAt_mono (W := W) h4
      have h6 := letsAt_mono (W := W) (show x₁ + d + 1 ≤ x₁ + d + d by omega)
      have h7 := letsAt_mono (W := W) hai
      have := hW.lets₂
      have := hW.lets₃
      omega
    omega

/-! ## The window `a R a R a` -/

lemma getElem?_append_at {A : Type} (P U : List A) (n : ℕ) (hn : n = P.length) :
    (P ++ U)[n]? = U[0]? := by
  subst hn; rw [List.getElem?_append_right le_rfl, Nat.sub_self]

lemma take_append_at {A : Type} (P U : List A) (n j : ℕ) (hn : n = P.length + j) :
    (P ++ U).take n = P ++ U.take j := by
  subst hn; exact List.take_length_add_append j

/-- A word of the form `A' a R a R a C'`, with `R` a balanced word of brackets, satisfies the
hypotheses of the core argument. -/
theorem window_of_decomp (A' R C' : List (TreeSym Unit)) (hR : lets R = 0) (hb : bal R = 0) :
    Window (A' ++ TreeSym.letter () :: (R ++ TreeSym.letter () :: (R ++ TreeSym.letter () :: C')))
      A'.length (R.length + 1) := by
  set ℓ : TreeSym Unit := TreeSym.letter ()
  set W := A' ++ ℓ :: (R ++ ℓ :: (R ++ ℓ :: C'))
  have e1 : W = (A' ++ [ℓ]) ++ (R ++ ℓ :: (R ++ ℓ :: C')) := by simp [W]
  have e2 : W = (A' ++ ℓ :: R) ++ (ℓ :: (R ++ ℓ :: C')) := by simp [W]
  have e3 : W = (A' ++ ℓ :: R ++ [ℓ]) ++ (R ++ ℓ :: C') := by simp [W]
  have e4 : W = (A' ++ ℓ :: R ++ ℓ :: R) ++ (ℓ :: C') := by simp [W]
  have hℓ : lets [ℓ] = 1 := rfl
  have hℓb : symBal ℓ = 0 := rfl
  have L0 : letsAt W A'.length = lets A' := by
    rw [letsAt, take_append_at A' _ A'.length 0 rfl]; simp
  have L1 : letsAt W (A'.length + 1) = lets A' + 1 := by
    rw [letsAt, take_append_at A' _ (A'.length + 1) 1 rfl]; simp [symLet, ℓ]
  have L2 : letsAt W (A'.length + (R.length + 1)) = lets A' + 1 := by
    rw [letsAt, e2, take_append_at _ _ _ 0
      (by simp only [List.length_append, List.length_cons]; omega)]
    simp [symLet, ℓ, hR]
  have L3 : letsAt W (A'.length + (R.length + 1) + 1) = lets A' + 2 := by
    rw [letsAt, e2, take_append_at _ _ _ 1
      (by simp only [List.length_append, List.length_cons])]
    simp [symLet, ℓ, hR]
  have L4 : letsAt W (A'.length + (R.length + 1) + (R.length + 1)) = lets A' + 2 := by
    rw [letsAt, e4, take_append_at _ _ _ 0
      (by simp only [List.length_append, List.length_cons]; omega)]
    simp [symLet, ℓ, hR]
  have L5 : letsAt W (A'.length + (R.length + 1) + (R.length + 1) + 1) = lets A' + 3 := by
    rw [letsAt, e4, take_append_at _ _ _ 1
      (by simp only [List.length_append, List.length_cons])]
    simp [symLet, ℓ, hR]
  refine ⟨by omega, ?_, ?_, by omega, by omega, by omega, by omega, ?_⟩
  · rw [getElem?_append_at A' _ _ rfl]; rfl
  · rw [e4, getElem?_append_at _ _ _
      (by simp only [List.length_append, List.length_cons])]
    rfl
  · intro j hj1 hj2
    obtain ⟨i, rfl⟩ : ∃ i, j = A'.length + 1 + i := ⟨j - A'.length - 1, by omega⟩
    have hi : i ≤ R.length := by omega
    rw [depthAt, depthAt]
    conv_lhs => rw [e3, take_append_at _ _ (A'.length + 1 + i + (R.length + 1)) i
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
      List.take_append_of_le_length hi]
    conv_rhs => rw [e1, take_append_at _ _ (A'.length + 1 + i) i
      (by simp only [List.length_append, List.length_singleton]),
      List.take_append_of_le_length hi]
    simp [hb, hℓb]

/-- No Simon tree for `capHom` has an encoding of the form `A' a R a R a C'` with `R` a balanced
word of brackets. -/
theorem no_simon_enc_window (A' R C' : List (TreeSym Unit)) (hR : lets R = 0) (hb : bal R = 0)
    (t : FactTree Unit) (ht : t.IsSimon capHom) :
    t.enc ≠ A' ++ TreeSym.letter () :: (R ++ TreeSym.letter () :: (R ++ TreeSym.letter () :: C')) := by
  intro he
  refine no_simon_over_window (window_of_decomp A' R C' hR hb) t ht 0 ⟨[], [], by simp [he], rfl⟩
    (Nat.zero_le _) ?_
  rw [he]
  simp
  omega

end Transducers.Exercises
