/-
Part D, Section *Evaluation*, subsection *Simon trees*: Lemma `lem:factorisation-forest-evaluation`
(what a Simon tree buys you).

The book's lemma says that, given a Simon tree, the value of the homomorphism on any factor of the
underlying string can be computed in time linear in the height of the tree.  The project has no
model of running time, so what is formalised is the content of the book's argument that does not
depend on one: **the value on a factor is a product of at most `2·height + 1` monoid elements, each
of which is the label of a node of the tree** (`Transducers.factorisation_forest_evaluation`).  The
algorithm of the book computes exactly such a product: at every level of the tree it combines a
bounded number of labels -- the labels of at most one bundle of consecutive fully covered siblings,
which under a node with three or more children is the idempotent itself, and of at most two
partially covered children, into which it descends.  The navigation that the book's data structure
supports in constant time (parent and sibling pointers, comparison of siblings) is what finds those
labels; it is not modelled here.

A factor of the underlying string `w` is given as a decomposition `w = u v x`, the factor being
`v`, rather than by its two endpoints.

Without the idempotent property the statement fails: under a node with many children, all of them
covered by the factor, the product of their labels need not be the label of any node.
-/
import RequestProject.PartD.SimonBound

namespace Transducers

namespace FactTree

variable {A M : Type} [Monoid M] (h : FreeMonoid A →* M)

/-- `Repr h P n m`: the monoid element `m` is a product of at most `n` labels of nodes of `P`. -/
def Repr (P : FactTree A) (n : ℕ) (m : M) : Prop :=
  ∃ l : List M, l.length ≤ n ∧ (∀ y ∈ l, ∃ s, IsSubtree s P ∧ label h s = y) ∧ l.prod = m

variable {h}

lemma Repr.mul {P : FactTree A} {n n' : ℕ} {m m' : M} (h₁ : Repr h P n m) (h₂ : Repr h P n' m') :
    Repr h P (n + n') (m * m') := by
  obtain ⟨l, hl, hl', rfl⟩ := h₁
  obtain ⟨l', hk, hk', rfl⟩ := h₂
  refine ⟨l ++ l', by simp; omega, ?_, by simp⟩
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hl' y hy
  · exact hk' y hy

lemma Repr.mono {P : FactTree A} {n n' : ℕ} {m : M} (h₁ : Repr h P n m) (hn : n ≤ n') :
    Repr h P n' m := by
  obtain ⟨l, hl, hl', rfl⟩ := h₁
  exact ⟨l, by omega, hl', rfl⟩

lemma Repr.lift {P P' : FactTree A} {n : ℕ} {m : M} (h₁ : Repr h P n m) (hP : IsSubtree P P') :
    Repr h P' n m := by
  obtain ⟨l, hl, hl', rfl⟩ := h₁
  refine ⟨l, hl, fun y hy => ?_, rfl⟩
  obtain ⟨s, hs, rfl⟩ := hl' y hy
  exact ⟨s, hs.trans hP, rfl⟩

lemma Repr.congr {P : FactTree A} {n : ℕ} {m m' : M} (h₁ : Repr h P n m) (he : m = m') :
    Repr h P n m' := he ▸ h₁

lemma repr_one (P : FactTree A) : Repr h P 0 1 := ⟨[], by simp, by simp, rfl⟩

lemma hv_append (u v : List A) :
    h (FreeMonoid.ofList (u ++ v)) = h (FreeMonoid.ofList u) * h (FreeMonoid.ofList v) := by
  rw [FreeMonoid.ofList_append, map_mul]

lemma hv_nil : h (FreeMonoid.ofList ([] : List A)) = 1 := by simp

lemma prod_labels (ys : List (FactTree A)) :
    (ys.map (label h)).prod = h (FreeMonoid.ofList (ys.map yield).flatten) := by
  induction ys with
  | nil => simp
  | cons c ys ih => simp [ih, label]

/-- The product of the labels of a list of siblings uses at most as many labels as there are
siblings. -/
lemma repr_labels {P : FactTree A} (ys : List (FactTree A)) (hsub : ∀ c ∈ ys, IsSubtree c P) :
    Repr h P ys.length (h (FreeMonoid.ofList (ys.map yield).flatten)) := by
  refine ⟨ys.map (label h), by simp, ?_, prod_labels ys⟩
  intro y hy
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
  exact ⟨c, hsub c hc, rfl⟩

lemma prod_cons_idem {e : M} (he : IsIdempotentElem e) :
    ∀ zs : List M, (∀ z ∈ zs, z = e) → (e :: zs).prod = e
  | [], _ => by simp
  | z :: zs, hz => by
    have hze := hz z (by simp)
    subst hze
    rw [List.prod_cons, prod_cons_idem he zs (fun y hy => hz y (by simp [hy]))]
    exact he.eq

/-- If siblings all carry the same idempotent label, their product is a single label. -/
lemma repr_labels_idem {P : FactTree A} (ys : List (FactTree A)) (hsub : ∀ c ∈ ys, IsSubtree c P)
    {e : M} (he : IsIdempotentElem e) (hl : ∀ c ∈ ys, label h c = e) :
    Repr h P 1 (h (FreeMonoid.ofList (ys.map yield).flatten)) := by
  rcases ys with _ | ⟨c, ys⟩
  · exact (repr_one P).mono (by omega) |>.congr (by simp)
  · refine ⟨[e], by simp, ?_, ?_⟩
    · intro y hy
      simp only [List.mem_singleton] at hy
      exact ⟨c, hsub c (by simp), by rw [hy, hl c (by simp)]⟩
    · rw [← prod_labels, List.map_cons, hl c (by simp), List.prod_singleton]
      exact (prod_cons_idem he (ys.map (label h)) (fun z hz => by
        obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
        exact hl z' (List.mem_cons_of_mem _ hz'))).symm

variable (h) in
/-- The sibling condition of a Simon tree, for a list of siblings: at most `k` of them, or all with
the same idempotent label. -/
def Sib (k : ℕ) (ys : List (FactTree A)) : Prop :=
  ys.length ≤ k ∨ ∃ e : M, IsIdempotentElem e ∧ ∀ c ∈ ys, label h c = e

lemma repr_sib {P : FactTree A} {k : ℕ} (hk : 1 ≤ k) {ys : List (FactTree A)} (hs : Sib h k ys)
    (hsub : ∀ c ∈ ys, IsSubtree c P) :
    Repr h P k (h (FreeMonoid.ofList (ys.map yield).flatten)) := by
  rcases hs with hs | ⟨e, he, hl⟩
  · exact (repr_labels ys hsub).mono hs
  · exact (repr_labels_idem ys hsub he hl).mono hk

lemma Sib.of_subset {k : ℕ} {ys zs : List (FactTree A)} (hs : Sib h k ys)
    (hsub : ∀ c ∈ zs, c ∈ ys) (hlen : zs.length + 1 ≤ ys.length) : Sib h (k - 1) zs := by
  rcases hs with hs | ⟨e, he, hl⟩
  · left; omega
  · right; exact ⟨e, he, fun c hc => hl c (hsub c hc)⟩

lemma Sib.of_subset' {k : ℕ} {ys zs : List (FactTree A)} (hs : Sib h k ys)
    (hsub : ∀ c ∈ zs, c ∈ ys) (hlen : zs.length ≤ ys.length) : Sib h k zs := by
  rcases hs with hs | ⟨e, he, hl⟩
  · left; omega
  · right; exact ⟨e, he, fun c hc => hl c (hsub c hc)⟩

/-- Splitting a concatenation of yields at a point. -/
lemma split_yields (ys : List (FactTree A)) (v x : List A) (hw : (ys.map yield).flatten = v ++ x) :
    (∃ ys₁ ys₂, ys = ys₁ ++ ys₂ ∧ v = (ys₁.map yield).flatten ∧ x = (ys₂.map yield).flatten) ∨
    (∃ ys₁ y ys₂ v' x', ys = ys₁ ++ y :: ys₂ ∧ y.yield = v' ++ x' ∧ x' ≠ [] ∧
      v = (ys₁.map yield).flatten ++ v' ∧ x = x' ++ (ys₂.map yield).flatten) := by
  rcases List.flatten_eq_append_iff.mp hw with ⟨as, bs, hab, rfl, rfl⟩ |
      ⟨as, bs, c, cs, ds, hab, rfl, rfl⟩
  · obtain ⟨ys₁, ys₂, rfl, h1, h2⟩ := List.map_eq_append_iff.mp hab
    left; exact ⟨ys₁, ys₂, rfl, by rw [h1], by rw [h2]⟩
  · obtain ⟨ys₁, ys₂', rfl, h1, h2⟩ := List.map_eq_append_iff.mp hab
    obtain ⟨y, ys₂, rfl, hy, h3⟩ := List.map_eq_cons_iff.mp h2
    right
    exact ⟨ys₁, y, ys₂, bs, c :: cs, rfl, hy, by simp, by rw [h1], by simp [h3]⟩

variable (h) in
/-- The prefix property of a tree: every prefix value is a product of at most `n` labels. -/
def PreP (P t : FactTree A) (n : ℕ) : Prop :=
  ∀ v x, t.yield = v ++ x → Repr h P n (h (FreeMonoid.ofList v))

variable (h) in
/-- The suffix property of a tree: every suffix value is a product of at most `n` labels. -/
def SufP (P t : FactTree A) (n : ℕ) : Prop :=
  ∀ u v, t.yield = u ++ v → Repr h P n (h (FreeMonoid.ofList v))

/-- Prefixes of a list of siblings. -/
lemma forest_pre {P : FactTree A} {H : ℕ} {ys : List (FactTree A)} (hs : Sib h 2 ys)
    (hsub : ∀ c ∈ ys, IsSubtree c P) (hpre : ∀ c ∈ ys, PreP h P c (H + 1))
    {v x : List A} (hw : (ys.map yield).flatten = v ++ x) :
    Repr h P (H + 2) (h (FreeMonoid.ofList v)) := by
  rcases split_yields ys v x hw with ⟨ys₁, ys₂, rfl, rfl, -⟩ |
      ⟨ys₁, y, ys₂, v', x', rfl, hy, -, rfl, -⟩
  · refine (repr_sib (by omega) (hs.of_subset' (fun c hc => by simp [hc]) (by simp))
      (fun c hc => hsub c (by simp [hc]))).mono (by omega)
  · rw [hv_append]
    have h₁ : Repr h P 1 (h (FreeMonoid.ofList (ys₁.map yield).flatten)) :=
      repr_sib le_rfl (hs.of_subset (fun c hc => by simp [hc]) (by simp))
        (fun c hc => hsub c (by simp [hc]))
    have h₂ := hpre y (by simp) v' x' hy
    exact (h₁.mul h₂).mono (by omega)

/-- Suffixes of a list of siblings. -/
lemma forest_suf {P : FactTree A} {H : ℕ} {ys : List (FactTree A)} (hs : Sib h 2 ys)
    (hsub : ∀ c ∈ ys, IsSubtree c P) (hsuf : ∀ c ∈ ys, SufP h P c (H + 1))
    {u v : List A} (hw : (ys.map yield).flatten = u ++ v) :
    Repr h P (H + 2) (h (FreeMonoid.ofList v)) := by
  rcases split_yields ys u v hw with ⟨ys₁, ys₂, rfl, -, rfl⟩ |
      ⟨ys₁, y, ys₂, u', v', rfl, hy, -, -, rfl⟩
  · refine (repr_sib (by omega) (hs.of_subset' (fun c hc => by simp [hc]) (by simp))
      (fun c hc => hsub c (by simp [hc]))).mono (by omega)
  · rw [hv_append]
    have h₂ : Repr h P 1 (h (FreeMonoid.ofList (ys₂.map yield).flatten)) :=
      repr_sib le_rfl (hs.of_subset (fun c hc => by simp [hc]) (by simp))
        (fun c hc => hsub c (by simp [hc]))
    have h₁ := hsuf y (by simp) u' v' hy
    exact (h₁.mul h₂).mono (by omega)

lemma sib_of_isSimon {cs : List (FactTree A)} (ht : (node cs).IsSimon h) : Sib h 2 cs := by
  cases ht with
  | node _ _ hidem =>
    by_cases hlen : 3 ≤ cs.length
    · right; exact hidem hlen
    · left; omega

lemma children_of_isSimon {cs : List (FactTree A)} (ht : (node cs).IsSimon h) :
    ∀ c ∈ cs, c.IsSimon h := by
  cases ht with
  | node _ hc _ => exact hc

lemma height_eq {cs : List (FactTree A)} :
    (node cs).height = ((node cs).height - 1) + 1 := by
  have : 1 ≤ (node cs).height := by rw [height_node]; omega
  omega

lemma leaf_split {a : A} {v x : List A} (hw : [a] = v ++ x) : v = [] ∨ v = [a] := by
  rcases v with _ | ⟨b, v⟩
  · left; rfl
  · right
    simp only [List.cons_append, List.cons.injEq] at hw
    obtain ⟨rfl, hv⟩ := hw
    have hv := List.append_eq_nil_iff.mp hv.symm
    rw [hv.1]

lemma repr_leaf {a : A} {v : List A} (hv : v = [] ∨ v = [a]) :
    Repr h (leaf a) 1 (h (FreeMonoid.ofList v)) := by
  rcases hv with rfl | rfl
  · exact (repr_one _).mono (by omega) |>.congr (by simp)
  · exact ⟨[label h (leaf a)], by simp, fun y hy => ⟨leaf a, IsSubtree.refl _, (List.mem_singleton.mp hy).symm⟩,
      by simp [label]⟩

/-- Every prefix value of a Simon tree is a product of at most `height + 1` labels. -/
theorem pre_of_isSimon {t : FactTree A} (ht : t.IsSimon h) : PreP h t t (t.height + 1) := by
  induction ht with
  | leaf a =>
    intro v x hw
    exact (repr_leaf (h := h) (leaf_split (by simpa using hw))).mono (by simp)
  | node cs hc hidem ih =>
    intro v x hw
    have hS : (node cs).IsSimon h := IsSimon.node cs hc hidem
    rw [yield_node] at hw
    have := forest_pre (H := (node cs).height - 1) (sib_of_isSimon hS)
      (fun c hc' => IsSubtree.child hc' (IsSubtree.refl c))
      (fun c hc' v' x' hw' => ((ih c hc' v' x' hw').lift
        (IsSubtree.child hc' (IsSubtree.refl c))).mono (by
          have := height_le_of_mem hc'; omega)) hw
    exact this.mono (by rw [height_eq (cs := cs)]; omega)

/-- Every suffix value of a Simon tree is a product of at most `height + 1` labels. -/
theorem suf_of_isSimon {t : FactTree A} (ht : t.IsSimon h) : SufP h t t (t.height + 1) := by
  induction ht with
  | leaf a =>
    intro u v hw
    rcases u with _ | ⟨b, u⟩
    · simp only [List.nil_append, yield_leaf] at hw
      exact (repr_leaf (h := h) (Or.inr hw.symm)).mono (by simp)
    · simp only [yield_leaf, List.cons_append, List.cons.injEq] at hw
      obtain ⟨-, hv⟩ := hw
      have hv := List.append_eq_nil_iff.mp hv.symm
      exact (repr_leaf (h := h) (Or.inl hv.2)).mono (by simp)
  | node cs hc hidem ih =>
    intro u v hw
    have hS : (node cs).IsSimon h := IsSimon.node cs hc hidem
    rw [yield_node] at hw
    have := forest_suf (H := (node cs).height - 1) (sib_of_isSimon hS)
      (fun c hc' => IsSubtree.child hc' (IsSubtree.refl c))
      (fun c hc' u' v' hw' => ((ih c hc' u' v' hw').lift
        (IsSubtree.child hc' (IsSubtree.refl c))).mono (by
          have := height_le_of_mem hc'; omega)) hw
    exact this.mono (by rw [height_eq (cs := cs)]; omega)

/-- Every factor value of a Simon tree is a product of at most `2·height + 1` labels. -/
theorem factor_of_isSimon {t : FactTree A} (ht : t.IsSimon h) :
    ∀ u v x, t.yield = u ++ v ++ x → Repr h t (2 * t.height + 1) (h (FreeMonoid.ofList v)) := by
  induction ht with
  | leaf a =>
    intro u v x hw
    rcases u with _ | ⟨b, u⟩
    · simp only [List.nil_append, yield_leaf] at hw
      exact (repr_leaf (h := h) (leaf_split hw)).mono (by simp)
    · simp only [yield_leaf, List.cons_append, List.cons.injEq] at hw
      obtain ⟨-, hv⟩ := hw
      have hv := List.append_eq_nil_iff.mp hv.symm
      have hv' := List.append_eq_nil_iff.mp hv.1
      exact (repr_leaf (h := h) (Or.inl hv'.2)).mono (by simp)
  | node cs hc hidem ih =>
    intro u v x hw
    have hS : (node cs).IsSimon h := IsSimon.node cs hc hidem
    set H := (node cs).height - 1 with hH
    have hHn : (node cs).height = H + 1 := height_eq
    have hsub : ∀ c ∈ cs, IsSubtree c (node cs) := fun c hc' => IsSubtree.child hc' (IsSubtree.refl c)
    have hhc : ∀ c ∈ cs, c.height ≤ H := fun c hc' => by have := height_le_of_mem hc'; omega
    have hpre : ∀ c ∈ cs, PreP h (node cs) c (H + 1) := fun c hc' v' x' hw' =>
      ((pre_of_isSimon (hc c hc') v' x' hw').lift (hsub c hc')).mono (by have := hhc c hc'; omega)
    have hsuf : ∀ c ∈ cs, SufP h (node cs) c (H + 1) := fun c hc' u' v' hw' =>
      ((suf_of_isSimon (hc c hc') u' v' hw').lift (hsub c hc')).mono (by have := hhc c hc'; omega)
    rw [hHn]
    rw [yield_node, List.append_assoc] at hw
    rcases split_yields cs u (v ++ x) hw with ⟨ys₁, ys₂, rfl, -, hvx⟩ |
        ⟨ys₁, y, ys₂, u', r, rfl, hy, -, -, hvx⟩
    · -- the factor starts at a child boundary
      have := forest_pre (H := H) ((sib_of_isSimon hS).of_subset' (fun c hc' => by simp [hc'])
        (by simp)) (fun c hc' => hsub c (by simp [hc'])) (fun c hc' => hpre c (by simp [hc']))
        hvx.symm
      exact this.mono (by omega)
    · rcases List.append_eq_append_iff.mp hvx with ⟨a', hra, hxa⟩ | ⟨c', hvr, hrc⟩
      · -- the factor lies inside the child `y`
        have hyy : y.yield = u' ++ v ++ a' := by rw [hy, hra, List.append_assoc]
        have := ((ih y (by simp) u' v a' hyy).lift (hsub y (by simp)))
        exact this.mono (by have := hhc y (by simp); omega)
      · -- the factor spans: a suffix of `y`, then a prefix of the following siblings
        rw [hvr, hv_append]
        have h₁ := hsuf y (by simp) u' r hy
        have h₂ := forest_pre (H := H) ((sib_of_isSimon hS).of_subset' (fun c hc' => by simp [hc'])
          (by simp; omega)) (fun c hc' => hsub c (by simp [hc'])) (fun c hc' => hpre c (by simp [hc']))
          hrc
        exact (h₁.mul h₂).mono (by omega)

end FactTree

/-- **Lemma `lem:factorisation-forest-evaluation`** (evaluating factors with a Simon tree), in the
form that does not depend on a model of running time.  Given a Simon tree `t` for a monoid
homomorphism `h`, the value of `h` on any factor `v` of the underlying string `u v x` is the product
of a list of at most `2·height(t) + 1` monoid elements, each of which is the label of a node of
`t` (the value of `h` on the subtree rooted at that node).  So the value is obtained from the labels
stored in the tree with a number of monoid operations linear in the height, which is what the
book's algorithm does; the navigation of the tree is not modelled. -/
theorem factorisation_forest_evaluation {A M : Type} [Monoid M] (h : FreeMonoid A →* M)
    {t : FactTree A} (ht : t.IsSimon h) (u v x : List A) (hw : t.yield = u ++ v ++ x) :
    ∃ l : List M, l.length ≤ 2 * t.height + 1 ∧
      (∀ m ∈ l, ∃ s : FactTree A, s.IsSubtree t ∧ s.label h = m) ∧
      l.prod = h (FreeMonoid.ofList v) :=
  FactTree.factor_of_isSimon ht u v x hw

end Transducers
