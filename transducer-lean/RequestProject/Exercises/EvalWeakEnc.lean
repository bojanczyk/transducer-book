/-
Exercise `exer:weak-simon-tree-aperiodic` of Part D, Section *Evaluation*
(`partDPolyregular/evaluation.tex`): the generic machinery.

* `Transducers.FactTree.IsWeakSimon`: the *weak Simon trees* of the exercise (a node with at least
  three children has all its children labelled by the same monoid element, which need not be an
  idempotent), and its working form `Transducers.Exercises.WS` for a valuation of the letters.
* `Transducers.Exercises.encR`: the bracket encoding (`Transducers.FactTree.enc`) of a tree all of
  whose leaves have the same depth `K + 1`, written through *ranks*: between two consecutive
  letters the encoding contains `]ʳ [ʳ` for some rank `r`, the number of nodes that are closed (and
  opened) there.
* `Transducers.Exercises.rk`: the ranks computed from a monoid valuation `ψ : X → N` and a function
  `G : N → N → ℕ` -- the rank between two letters is `G` of the value of the prefix and of the value
  of the suffix (in a context `α`, `β`).  When `N` is finite and aperiodic, such ranks are what an
  aperiodic bimachine can produce.
* `Transducers.Exercises.Rep`: a tree is a weak Simon tree of uniform depth whose encoding is
  given by these ranks; and the closure of `Rep` under the constructions of the proof: unary nodes,
  binary nodes, flat nodes, and substitution of trees for the leaves of a tree.
-/
import RequestProject.PartD.SimonRat

namespace Transducers

namespace FactTree

variable {A : Type}

/-- **Weak Simon tree** (Exercise `exer:weak-simon-tree-aperiodic`).  A factorisation tree for the
monoid homomorphism `h` is a weak Simon tree if every node with at least three children has all its
children labelled by the same monoid element -- which, unlike for a Simon tree
(`Transducers.FactTree.IsSimon`), need not be an idempotent. -/
inductive IsWeakSimon {M : Type*} [Monoid M] (h : FreeMonoid A →* M) : FactTree A → Prop
  | leaf (a : A) : IsWeakSimon h (leaf a)
  | node (cs : List (FactTree A)) :
      (∀ c ∈ cs, IsWeakSimon h c) →
      (3 ≤ cs.length → ∃ m : M, ∀ c ∈ cs, label h c = m) →
      IsWeakSimon h (node cs)

/-- Every Simon tree is a weak Simon tree. -/
lemma IsSimon.isWeakSimon {M : Type*} [Monoid M] {h : FreeMonoid A →* M} :
    ∀ {t : FactTree A}, t.IsSimon h → t.IsWeakSimon h
  | _, .leaf a => .leaf a
  | _, .node cs hc h3 => .node cs (fun c hc' => (hc c hc').isWeakSimon)
      (fun h3' => (h3 h3').imp fun _ he => he.2)

end FactTree

namespace Exercises

open FactTree TreeSym Simon

variable {X Y M N N' : Type} [Monoid M] [Monoid N] [Monoid N']

/-! ## Weak Simon trees for a valuation of the letters -/

/-- Weak Simon trees for a valuation `φ` of the letters. -/
inductive WS (φ : X → M) : FactTree X → Prop
  | leaf (x : X) : WS φ (.leaf x)
  | node (cs : List (FactTree X)) : (∀ c ∈ cs, WS φ c) →
      (3 ≤ cs.length → ∃ m : M, ∀ c ∈ cs, val φ c.yield = m) → WS φ (.node cs)

lemma WS.isWeakSimon {A : Type} {h : FreeMonoid A →* M} :
    ∀ {t : FactTree A}, WS (fun a => h (FreeMonoid.of a)) t → t.IsWeakSimon h
  | _, .leaf a => .leaf a
  | _, .node cs hc h3 => .node cs (fun c hc' => (hc c hc').isWeakSimon) (fun h3' => by
      obtain ⟨m, hm⟩ := h3 h3'
      exact ⟨m, fun c hc' => by rw [label, hom_ofList]; exact hm c hc'⟩)

/-! ## The encoding of a tree of uniform depth, through ranks -/

/-- The part of the encoding after the first letter: rank `r` before the letter `x` contributes
`]ʳ [ʳ x`. -/
def body (rest : List (ℕ × X)) : List (TreeSym X) :=
  rest.flatMap fun p => List.replicate p.1 cl ++ List.replicate p.1 op ++ [letter p.2]

/-- The encoding of a tree whose leaves all have depth `K + 1`, with first letter `x0` and the
ranks and letters `rest` after it. -/
def encR (K : ℕ) (x0 : X) (rest : List (ℕ × X)) : List (TreeSym X) :=
  List.replicate (K + 1) op ++ letter x0 :: body rest ++ List.replicate (K + 1) cl

@[simp] lemma body_nil : body ([] : List (ℕ × X)) = [] := rfl

lemma body_cons (p : ℕ × X) (rest : List (ℕ × X)) :
    body (p :: rest) = List.replicate p.1 cl ++ List.replicate p.1 op ++ [letter p.2] ++
      body rest := by
  simp [body]

lemma body_append (r s : List (ℕ × X)) : body (r ++ s) = body r ++ body s := by
  simp [body, List.flatMap_append]

/-! ## Ranks computed from the values of the prefix and of the suffix -/

/-- The ranks between the letters of `x0 :: xs`, in the context `α` (on the left) and `β` (on the
right): the rank before a letter is `G (α · value of the prefix) (value of the suffix · β)`. -/
def rk (ψ : X → N) (G : N → N → ℕ) : N → X → List X → N → List (ℕ × X)
  | _, _, [], _ => []
  | α, x0, x1 :: xs, β => (G (α * ψ x0) (val ψ (x1 :: xs) * β), x1) :: rk ψ G (α * ψ x0) x1 xs β

@[simp] lemma rk_nil (ψ : X → N) (G : N → N → ℕ) (α : N) (x0 : X) (β : N) :
    rk ψ G α x0 [] β = [] := rfl

lemma rk_cons (ψ : X → N) (G : N → N → ℕ) (α : N) (x0 x1 : X) (xs : List X) (β : N) :
    rk ψ G α x0 (x1 :: xs) β =
      (G (α * ψ x0) (val ψ (x1 :: xs) * β), x1) :: rk ψ G (α * ψ x0) x1 xs β := rfl

lemma rk_append (ψ : X → N) (G : N → N → ℕ) (y0 : X) (ys : List X) :
    ∀ (α : N) (x0 : X) (xs : List X) (β : N),
      rk ψ G α x0 (xs ++ y0 :: ys) β = rk ψ G α x0 xs (val ψ (y0 :: ys) * β) ++
        (G (α * val ψ (x0 :: xs)) (val ψ (y0 :: ys) * β), y0) ::
          rk ψ G (α * val ψ (x0 :: xs)) y0 ys β
  | α, x0, [], β => by simp [rk_cons]
  | α, x0, x1 :: xs, β => by
    rw [List.cons_append, rk_cons, rk_append ψ G y0 ys (α * ψ x0) x1 xs β, rk_cons]
    simp [mul_assoc]

lemma rk_congr {ψ : X → N} {ψ' : X → N'} {G : N → N → ℕ} {G' : N' → N' → ℕ} (F : ℕ → ℕ) :
    ∀ (xs : List X) (α : N) (α' : N') (x0 : X) (β : N) (β' : N'),
      (∀ u v : List X, u ≠ [] → v ≠ [] → u ++ v = x0 :: xs →
        G (α * val ψ u) (val ψ v * β) = F (G' (α' * val ψ' u) (val ψ' v * β'))) →
      rk ψ G α x0 xs β = (rk ψ' G' α' x0 xs β').map (fun p => (F p.1, p.2))
  | [], _, _, _, _, _, _ => rfl
  | x1 :: xs, α, α', x0, β, β', h => by
    rw [rk_cons, rk_cons, List.map_cons]
    congr 1
    · have := h [x0] (x1 :: xs) (by simp) (by simp) rfl
      simp only [val_singleton] at this
      rw [this]
    · refine rk_congr F xs _ _ x1 β β' fun u v hu hv huv => ?_
      have := h (x0 :: u) v (by simp) hv (by rw [List.cons_append, huv])
      simpa [mul_assoc] using this

lemma rk_const (ψ : X → N) (c : ℕ) :
    ∀ (xs : List X) (α : N) (x0 : X) (β : N), rk ψ (fun _ _ => c) α x0 xs β = xs.map (c, ·)
  | [], _, _, _ => rfl
  | x1 :: xs, α, x0, β => by rw [rk_cons, rk_const ψ c xs, List.map_cons]

/-! ## Representations -/

/-- `Rep φ ψ G K α β t w`: `t` is a weak Simon tree for `φ` with underlying string `w` (nonempty),
of height at most `K + 1`, and its encoding is `encR K` with the ranks computed by `ψ` and `G` in
the context `α`, `β`. -/
def Rep (φ : X → M) (ψ : X → N) (G : N → N → ℕ) (K : ℕ) (α β : N) (t : FactTree X)
    (w : List X) : Prop :=
  t.yield = w ∧ WS φ t ∧ t.height ≤ K + 1 ∧
    ∃ x0 xs, w = x0 :: xs ∧ t.enc = encR K x0 (rk ψ G α x0 xs β)

lemma Rep.ne_nil {φ : X → M} {ψ : X → N} {G : N → N → ℕ} {K : ℕ} {α β : N} {t : FactTree X}
    {w : List X} (h : Rep φ ψ G K α β t w) : w ≠ [] := by
  obtain ⟨-, -, -, x0, xs, rfl, -⟩ := h
  simp

/-- Transport of a representation along a change of the rank function. -/
lemma Rep.congr {φ : X → M} {ψ : X → N} {ψ' : X → N'} {G : N → N → ℕ} {G' : N' → N' → ℕ}
    {K : ℕ} {α β : N} {α' β' : N'} {t : FactTree X} {w : List X} (h : Rep φ ψ' G' K α' β' t w)
    (hG : ∀ u v : List X, u ≠ [] → v ≠ [] → u ++ v = w →
      G (α * val ψ u) (val ψ v * β) = G' (α' * val ψ' u) (val ψ' v * β')) :
    Rep φ ψ G K α β t w := by
  obtain ⟨hy, hws, hh, x0, xs, rfl, he⟩ := h
  refine ⟨hy, hws, hh, x0, xs, rfl, ?_⟩
  rw [he, rk_congr id xs α' α x0 β' β (fun u v hu hv huv => (hG u v hu hv huv).symm)]
  simp

/-! ### Unary nodes -/

lemma encR_succ (K : ℕ) (x0 : X) (r : List (ℕ × X)) :
    encR (K + 1) x0 r = [op] ++ encR K x0 r ++ [cl] := by
  rw [encR, encR, List.replicate_succ (a := op) (n := K + 1),
    List.replicate_succ' (a := cl) (n := K + 1)]
  simp

lemma encR_append (K : ℕ) (x0 y0 : X) (r₁ r₂ : List (ℕ × X)) :
    encR K x0 r₁ ++ encR K y0 r₂ = encR K x0 (r₁ ++ (K + 1, y0) :: r₂) := by
  simp [encR, body_append, body_cons]

lemma enc_node_single {K : ℕ} {t : FactTree X} {x0 : X} {r : List (ℕ × X)}
    (h : t.enc = encR K x0 r) : (FactTree.node [t]).enc = encR (K + 1) x0 r := by
  rw [enc_node, encR_succ, ← h]
  simp

lemma Rep.pad {φ : X → M} {ψ : X → N} {G : N → N → ℕ} {K : ℕ} {α β : N} {t : FactTree X}
    {w : List X} (h : Rep φ ψ G K α β t w) : Rep φ ψ G (K + 1) α β (.node [t]) w := by
  obtain ⟨hy, hws, hh, x0, xs, rfl, he⟩ := h
  refine ⟨by simp [hy], WS.node _ (by simpa using hws) (by simp), ?_, x0, xs, rfl,
    enc_node_single he⟩
  exact height_node_le (by simpa using hh)

/-- `padT n t`: the tree `t` under `n` unary nodes. -/
def padT : ℕ → FactTree X → FactTree X
  | 0, t => t
  | n + 1, t => .node [padT n t]

lemma Rep.padN {φ : X → M} {ψ : X → N} {G : N → N → ℕ} {K : ℕ} {α β : N} {t : FactTree X}
    {w : List X} (h : Rep φ ψ G K α β t w) : ∀ n, Rep φ ψ G (K + n) α β (padT n t) w
  | 0 => h
  | n + 1 => by rw [← add_assoc]; exact (Rep.padN h n).pad

lemma Rep.padTo {φ : X → M} {ψ : X → N} {G : N → N → ℕ} {K K' : ℕ} {α β : N} {t : FactTree X}
    {w : List X} (h : Rep φ ψ G K α β t w) (hK : K ≤ K') :
    Rep φ ψ G K' α β (Exercises.padT (K' - K) t) w := by
  have := h.padN (K' - K)
  rwa [Nat.add_sub_cancel' hK] at this

/-! ### Binary nodes -/

lemma enc_node_two {K : ℕ} {t₁ t₂ : FactTree X} {x0 y0 : X} {r₁ r₂ : List (ℕ × X)}
    (h₁ : t₁.enc = encR K x0 r₁) (h₂ : t₂.enc = encR K y0 r₂) :
    (FactTree.node [t₁, t₂]).enc = encR (K + 1) x0 (r₁ ++ (K + 1, y0) :: r₂) := by
  rw [enc_node, encR_succ, ← encR_append, ← h₁, ← h₂]
  simp

lemma Rep.two {φ : X → M} {ψ : X → N} {G : N → N → ℕ} {K : ℕ} {α β : N} {t₁ t₂ : FactTree X}
    {u v : List X} (h₁ : Rep φ ψ G K α (val ψ v * β) t₁ u)
    (h₂ : Rep φ ψ G K (α * val ψ u) β t₂ v) (hG : G (α * val ψ u) (val ψ v * β) = K + 1) :
    Rep φ ψ G (K + 1) α β (.node [t₁, t₂]) (u ++ v) := by
  obtain ⟨hy₁, hws₁, hh₁, x0, xs, rfl, he₁⟩ := h₁
  obtain ⟨hy₂, hws₂, hh₂, y0, ys, rfl, he₂⟩ := h₂
  refine ⟨by simp [hy₁, hy₂], WS.node _ ?_ (by simp), ?_, x0, xs ++ y0 :: ys, by simp, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hws₁
    · exact hws₂
  · refine height_node_le fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> assumption
  · rw [enc_node_two he₁ he₂, rk_append, hG]

/-! ### Flat nodes -/

/-- The flat tree: all letters are children of the root. -/
def flat (w : List X) : FactTree X := .node (w.map .leaf)

lemma body_map_zero (xs : List X) : body (xs.map ((0 : ℕ), ·)) = xs.map letter := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [body_cons, ih]

lemma Rep.flat {φ : X → M} {ψ : X → N} {G : N → N → ℕ} {α β : N} {w : List X} {s : M}
    (hw : w ≠ []) (hs : ∀ x ∈ w, φ x = s)
    (hG : ∀ u v : List X, u ≠ [] → v ≠ [] → u ++ v = w → G (α * val ψ u) (val ψ v * β) = 0) :
    Rep φ ψ G 0 α β (Exercises.flat w) w := by
  obtain ⟨x0, xs, rfl⟩ := List.exists_cons_of_ne_nil hw
  refine ⟨?_, WS.node _ ?_ ?_, ?_, x0, xs, rfl, ?_⟩
  · have : ∀ l : List X, ((l.map FactTree.leaf).map yield).flatten = l := by
      intro l
      induction l with
      | nil => rfl
      | cons x l ih => simpa using ih
    simpa [Exercises.flat] using this (x0 :: xs)
  · intro c hc
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hc
    exact WS.leaf x
  · intro _
    refine ⟨s, fun c hc => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    simpa using hs x hx
  · refine height_node_le fun c hc => ?_
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hc
    simp
  · rw [rk_congr (G' := fun (_ _ : Unit) => 0) (ψ' := fun _ => ()) (fun _ => 0) xs α () x0 β ()
      (fun u v hu hv huv => hG u v hu hv huv), rk_const, List.map_map]
    rw [Exercises.flat, enc_node, encR]
    have : ((fun p : ℕ × X => (0, p.2)) ∘ ((0 : ℕ), ·)) = ((0 : ℕ), ·) := rfl
    rw [this, body_map_zero]
    have h2 : ∀ l : List X, (l.map fun x => [letter x]).flatten = l.map letter := by
      intro l
      induction l with
      | nil => rfl
      | cons x l ih => simp [ih]
    simp [List.map_map, Function.comp_def, h2]

/-! ### Substitution of trees for the leaves of a tree -/

/-- Substitution of the tree `f y` for every leaf `y`. -/
def subst (f : Y → FactTree X) : FactTree Y → FactTree X
  | .leaf y => f y
  | .node cs => .node (cs.map (subst f))

/-- The substitution on the symbols of an encoding. -/
def symSub (f : Y → FactTree X) : TreeSym Y → List (TreeSym X)
  | letter y => (f y).enc
  | op => [op]
  | cl => [cl]

theorem yield_subst (f : Y → FactTree X) :
    ∀ t : FactTree Y, (subst f t).yield = t.yield.flatMap (fun y => (f y).yield)
  | .leaf y => by simp [subst]
  | .node cs => by
    rw [subst, yield_node, yield_node, List.map_map, Simon.flatMap_flatten, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    have := List.sizeOf_lt_of_mem hc
    exact yield_subst f c

theorem enc_subst (f : Y → FactTree X) :
    ∀ t : FactTree Y, (subst f t).enc = t.enc.flatMap (symSub f)
  | .leaf y => by simp [subst, symSub]
  | .node cs => by
    rw [subst, enc_node, enc_node, List.map_map]
    simp only [List.flatMap_append, Simon.flatMap_flatten, List.map_map]
    have : ∀ c ∈ cs, (enc ∘ subst f) c = ((fun u => u.flatMap (symSub f)) ∘ enc) c := by
      intro c hc
      have := List.sizeOf_lt_of_mem hc
      exact enc_subst f c
    rw [List.map_congr_left this]
    simp [symSub]

lemma mem_yield_of_mem {y : Y} {c : FactTree Y} {cs : List (FactTree Y)} (hc : c ∈ cs)
    (hy : y ∈ c.yield) : y ∈ (FactTree.node cs).yield := by
  rw [yield_node]
  exact List.mem_flatten.mpr ⟨c.yield, List.mem_map_of_mem hc, hy⟩

theorem height_subst (f : Y → FactTree X) (H : ℕ) :
    ∀ t : FactTree Y, (∀ y ∈ t.yield, (f y).height ≤ H) → (subst f t).height ≤ t.height + H
  | .leaf y, h => by simpa [subst] using h y (by simp)
  | .node cs, h => by
    rw [subst]
    have h1 : 1 ≤ (FactTree.node cs).height := by rw [height_node]; omega
    have : ∀ c ∈ cs.map (subst f), c.height ≤ (FactTree.node cs).height - 1 + H := by
      intro c' hc'
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
      have := List.sizeOf_lt_of_mem hc
      have h2 := height_subst f H c fun y hy => h y (mem_yield_of_mem hc hy)
      have h3 := height_le_of_mem hc
      omega
    have := height_node_le this
    omega

lemma val_flatMap' (φ : X → M) (g : Y → List X) (l : List Y) :
    val φ (l.flatMap g) = (l.map fun y => val φ (g y)).prod := by
  induction l with
  | nil => simp
  | cons y l ih => simp [ih]

theorem ws_subst (f : Y → FactTree X) (φ : X → M) (φ' : Y → M) :
    ∀ t : FactTree Y, WS φ' t → (∀ y ∈ t.yield, WS φ (f y) ∧ val φ (f y).yield = φ' y) →
      WS φ (subst f t)
  | .leaf y, _, h => by simpa [subst] using (h y (by simp)).1
  | .node cs, hws, h => by
    rw [subst]
    cases hws with
    | node _ hc h3 =>
      refine WS.node _ ?_ ?_
      · intro c' hc'
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hc'
        have := List.sizeOf_lt_of_mem hcm
        exact ws_subst f φ φ' c (hc c hcm) fun y hy => h y (mem_yield_of_mem hcm hy)
      · intro hlen
        rw [List.length_map] at hlen
        obtain ⟨m, hm⟩ := h3 hlen
        refine ⟨m, fun c' hc' => ?_⟩
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hc'
        rw [yield_subst, val_flatMap', ← hm c hcm, val]
        congr 1
        apply List.map_congr_left
        intro y hy
        exact (h y (mem_yield_of_mem hcm hy)).2

lemma flatMap_symSub_rep (f : Y → FactTree X) (n : ℕ) :
    (List.replicate n (op : TreeSym Y)).flatMap (symSub f) = List.replicate n op ∧
      (List.replicate n (cl : TreeSym Y)).flatMap (symSub f) = List.replicate n cl := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, symSub, ih.1, ih.2]

lemma flatMap_symSub_body (f : Y → FactTree X) (R : List (ℕ × Y)) :
    (body R).flatMap (symSub f) =
      R.flatMap fun p => List.replicate p.1 cl ++ List.replicate p.1 op ++ (f p.2).enc := by
  induction R with
  | nil => simp
  | cons p R ih =>
    rw [body_cons, List.flatMap_append, List.flatMap_append, List.flatMap_append, ih,
      (flatMap_symSub_rep f _).1, (flatMap_symSub_rep f _).2, List.flatMap_cons]
    simp [symSub]

lemma flatMap_symSub_body_rk (f : List X → FactTree X) (ψ : X → N) (G : N → N → ℕ)
    (ψO : List X → N') (GO : N' → N' → ℕ) (Kb K0 : ℕ) :
    ∀ (vs : List (List X)) (αO βO : N') (α β : N) (y0 : X) (ys : List X),
      (∀ pre y post, pre ++ y :: post = (y0 :: ys) :: vs → ∃ z0 zs, y = z0 :: zs ∧
        (f y).enc = encR Kb z0 (rk ψ G (α * val ψ pre.flatten) z0 zs
          (val ψ post.flatten * β))) →
      (∀ pre post, pre ≠ [] → post ≠ [] → pre ++ post = (y0 :: ys) :: vs →
        G (α * val ψ pre.flatten) (val ψ post.flatten * β) =
          GO (αO * val ψO pre) (val ψO post * βO) + Kb + 1) →
      (f (y0 :: ys)).enc ++ (body (rk ψO GO αO (y0 :: ys) vs βO)).flatMap (symSub f) ++
          List.replicate (K0 + 1) cl =
        List.replicate (Kb + 1) op ++ letter y0 ::
          body (rk ψ G α y0 (ys ++ vs.flatten) β) ++ List.replicate (K0 + Kb + 2) cl
  | [], αO, βO, α, β, y0, ys, HB, _ => by
    obtain ⟨z0, zs, hz, he⟩ := HB [] (y0 :: ys) [] rfl
    obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hz
    rw [he]
    simp only [List.flatten_nil, val_nil, mul_one, one_mul, rk_nil, body_nil, List.flatMap_nil,
      List.append_nil, encR]
    rw [show K0 + Kb + 2 = (Kb + 1) + (K0 + 1) by omega, List.replicate_add]
    simp
  | (v1 :: vs), αO, βO, α, β, y0, ys, HB, HJ => by
    obtain ⟨y1, ys1, rfl, -⟩ := HB [y0 :: ys] v1 vs rfl
    have IH := flatMap_symSub_body_rk f ψ G ψO GO Kb K0 vs (αO * ψO (y0 :: ys)) βO
      (α * val ψ (y0 :: ys)) β y1 ys1
      (fun pre y post h => by
        obtain ⟨z0, zs, hz, he⟩ := HB ((y0 :: ys) :: pre) y post (by rw [List.cons_append, h])
        exact ⟨z0, zs, hz, by simpa [mul_assoc] using he⟩)
      (fun pre post hpre hpost h => by
        have := HJ ((y0 :: ys) :: pre) post (by simp) hpost (by rw [List.cons_append, h])
        simpa [mul_assoc] using this)
    obtain ⟨z0, zs, hz, he⟩ := HB [] (y0 :: ys) ((y1 :: ys1) :: vs) rfl
    obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hz
    have hJ := HJ [y0 :: ys] ((y1 :: ys1) :: vs) (by simp) (by simp) rfl
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, val_nil, mul_one,
      val_singleton] at he hJ
    set r := GO (αO * ψO (y0 :: ys)) (val ψO ((y1 :: ys1) :: vs) * βO) with hr
    have hR1 : List.replicate (r + Kb + 1) (cl : TreeSym X) =
        List.replicate (Kb + 1) cl ++ List.replicate r cl := by
      rw [show r + Kb + 1 = (Kb + 1) + r by omega, List.replicate_add]
    have hR2 : List.replicate (r + Kb + 1) (op : TreeSym X) =
        List.replicate r op ++ List.replicate (Kb + 1) op := by
      rw [add_assoc, List.replicate_add]
    rw [rk_cons, flatMap_symSub_body, List.flatMap_cons, ← flatMap_symSub_body, ← hr]
    dsimp only
    rw [List.flatten_cons, List.cons_append, rk_append]
    simp only [List.cons_append] at hJ he
    rw [hJ, he, encR, body_append, body_cons, hR1, hR2]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at IH ⊢
    rw [IH]

/-- **Substitution.**  If `T` is a tree for the string of blocks `v` (an outer tree, with ranks
computed by `ψO` and `GO`), and the tree `f y` represents the block `y` in its context, and the rank
between two blocks is the outer rank shifted by `Kb + 1`, then substituting the trees of the blocks
for the leaves of `T` gives a representation of the concatenation of the blocks. -/
lemma Rep.subst {φ : X → M} {ψ : X → N} {G : N → N → ℕ} {ψO : List X → N'} {GO : N' → N' → ℕ}
    {Ko Kb : ℕ} {α β : N} {T : FactTree (List X)} {v : List (List X)} (f : List X → FactTree X)
    (hT : T.yield = v) (hTws : WS (val φ) T) (hTh : T.height ≤ Ko + 1)
    (hTe : ∃ v0 vs, v = v0 :: vs ∧ T.enc = encR Ko v0 (rk ψO GO 1 v0 vs 1))
    (HB : ∀ pre y post, pre ++ y :: post = v →
      Rep φ ψ G Kb (α * val ψ pre.flatten) (val ψ post.flatten * β) (f y) y)
    (HJ : ∀ pre post, pre ≠ [] → post ≠ [] → pre ++ post = v →
      G (α * val ψ pre.flatten) (val ψ post.flatten * β) =
        GO (val ψO pre) (val ψO post) + Kb + 1) :
    Rep φ ψ G (Ko + Kb + 1) α β (subst f T) v.flatten := by
  obtain ⟨v0, vs, rfl, he⟩ := hTe
  have hmem : ∀ y ∈ v0 :: vs, ∃ a b, Rep φ ψ G Kb a b (f y) y := by
    intro y hy
    obtain ⟨pre, post, h⟩ := List.mem_iff_append.mp hy
    exact ⟨_, _, HB pre y post h.symm⟩
  obtain ⟨-, -, -, y0, ys, rfl, -⟩ := HB [] v0 vs rfl
  refine ⟨?_, ?_, ?_, y0, ys ++ vs.flatten, by simp, ?_⟩
  · rw [yield_subst, hT, List.flatMap_congr (g := id) (fun y hy => by
      obtain ⟨a, b, hr⟩ := hmem y hy
      exact hr.1), List.flatMap_def, List.map_id]
  · refine ws_subst f φ (val φ) T hTws fun y hy => ?_
    rw [hT] at hy
    obtain ⟨a, b, hr⟩ := hmem y hy
    exact ⟨hr.2.1, by rw [hr.1]⟩
  · have := height_subst f (Kb + 1) T fun y hy => by
      rw [hT] at hy
      obtain ⟨a, b, hr⟩ := hmem y hy
      exact hr.2.2.1
    omega
  · have key := flatMap_symSub_body_rk f ψ G ψO GO Kb Ko vs 1 1 α β y0 ys
      (fun pre y post h => by
        obtain ⟨-, -, -, z0, zs, hz, he'⟩ := HB pre y post h
        exact ⟨z0, zs, hz, he'⟩)
      (fun pre post hpre hpost h => by simpa using HJ pre post hpre hpost h)
    have hop : List.replicate (Ko + Kb + 1 + 1) (op : TreeSym X) =
        List.replicate (Ko + 1) op ++ List.replicate (Kb + 1) op := by
      rw [← List.replicate_add]; congr 1; omega
    rw [enc_subst, he, encR, List.flatMap_append, List.flatMap_append, List.flatMap_cons,
      (flatMap_symSub_rep f _).1, (flatMap_symSub_rep f _).2, encR, hop]
    simp only [symSub, List.append_assoc, List.cons_append] at key ⊢
    rw [key]

end Exercises

end Transducers
