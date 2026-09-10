/-
Part D, Section *A functional programming language*: Definition `def:majorants`.

A *majorant* for a type is the witness that the termination argument of Lemma
`lem:reduction-strategy-lemma` assigns to a term of that type; it is more than a number, and the
set of possible majorants depends on the type:

    Maj(1)      = ℕ                            |m|      = m
    Maj(A × B)  = Maj(A + B) = Maj A × Maj B   |(μ,ν)|  = max |μ| |ν|
    Maj(A*)     = Maj A
    Maj(A → B)  = ℕ × [Maj A → Maj B]          |(m,F)|  = m

where `[Maj A → Maj B]` is the set of monotone functions, and each `Maj A` is ordered
coordinatewise, and pointwise in the case of the function space.

The rendering here separates the underlying set from the monotonicity requirement:
`Transducers.Maj` uses *all* functions in the arrow case, `Transducers.Maj.le` is the order and
`Transducers.Maj.IsMono` is the (hereditary) monotonicity that makes an element of
`Transducers.Maj A` a majorant in the book's sense.  This is the usual way of avoiding a mutual
recursion between a set and an order on it, and nothing is lost: the book's `Maj A` is the
sub-collection cut out by `Transducers.Maj.IsMono`.

The book's assertions about these data are proved below: the order is a preorder
(`Transducers.Maj.le_refl`, `Transducers.Maj.le_trans`), the cost function is monotone
(`Transducers.Maj.cost_mono`), every two majorants have a least upper bound
(`Transducers.Maj.le_join_left`, `Transducers.Maj.le_join_right`, `Transducers.Maj.join_le`), the
operation `μ + r` is monotone and satisfies `|μ + r| = |μ| + r`
(`Transducers.Maj.cost_add`), and `⊤_A(m)` is a majorant, is monotone in `m` and has cost `m`
(`Transducers.Maj.isMono_top`, `Transducers.Maj.top_mono`, `Transducers.Maj.cost_top`).

This is the definition only.  Claim `claim:atomic-functions-majorised` and Claim
`claim:every-term-majorised`, which use it, are not formalised; see `THEOREMS.md`.
-/
import RequestProject.PartD.HONormal

namespace Transducers

/-- **Definition `def:majorants`.**  The set of majorants of a type.  In the arrow case this is
the set of *all* pairs (natural number, function); the monotonicity that the book requires of the
function is `Transducers.Maj.IsMono`. -/
@[reducible] def Maj : HTy → Type
  | .one => ℕ
  | .prod A B => Maj A × Maj B
  | .sum A B => Maj A × Maj B
  | .list A => Maj A
  | .arrow A B => ℕ × (Maj A → Maj B)

namespace Maj

/-- The order on majorants: on natural numbers the usual one, coordinatewise on pairs, and
pointwise on the function part of a majorant of arrow type. -/
def le : (A : HTy) → Maj A → Maj A → Prop
  | .one, m, n => m ≤ n
  | .prod A B, x, y => le A x.1 y.1 ∧ le B x.2 y.2
  | .sum A B, x, y => le A x.1 y.1 ∧ le B x.2 y.2
  | .list A, x, y => le A x y
  | .arrow _ B, x, y => x.1 ≤ y.1 ∧ ∀ z, le B (x.2 z) (y.2 z)

/-- **The cost `|μ|` of a majorant**: the largest natural number that appears in it. -/
def cost : (A : HTy) → Maj A → ℕ
  | .one, m => m
  | .prod A B, x => max (cost A x.1) (cost B x.2)
  | .sum A B, x => max (cost A x.1) (cost B x.2)
  | .list A, x => cost A x
  | .arrow _ _, x => x.1

/-- The monotonicity that the book requires of a majorant: the function part of a majorant of
arrow type is monotone, hereditarily. -/
def IsMono : (A : HTy) → Maj A → Prop
  | .one, _ => True
  | .prod A B, x => IsMono A x.1 ∧ IsMono B x.2
  | .sum A B, x => IsMono A x.1 ∧ IsMono B x.2
  | .list A, x => IsMono A x
  | .arrow A B, x =>
      (∀ z, IsMono A z → IsMono B (x.2 z)) ∧ (∀ z w, le A z w → le B (x.2 z) (x.2 w))

/-- The least upper bound `μ ∨ ν` of two majorants. -/
def join : (A : HTy) → Maj A → Maj A → Maj A
  | .one, m, n => max m n
  | .prod A B, x, y => (join A x.1 y.1, join B x.2 y.2)
  | .sum A B, x, y => (join A x.1 y.1, join B x.2 y.2)
  | .list A, x, y => join A x y
  | .arrow _ B, x, y => (max x.1 y.1, fun z => join B (x.2 z) (y.2 z))

/-- The majorant `μ + r`, obtained by adding `r` to every number that appears in `μ`. -/
def add : (A : HTy) → Maj A → ℕ → Maj A
  | .one, m, r => m + r
  | .prod A B, x, r => (add A x.1 r, add B x.2 r)
  | .sum A B, x, r => (add A x.1 r, add B x.2 r)
  | .list A, x, r => add A x r
  | .arrow _ B, x, r => (x.1 + r, fun z => add B (x.2 z) r)

/-- The majorant `⊤_A(m)` of Section *Expressive completeness*, which majorises the neutral terms
of type `A` whose arguments cost `m` in total. -/
def top : (A : HTy) → ℕ → Maj A
  | .one, m => m
  | .prod A B, m => (top A m, top B m)
  | .sum A B, m => (top A m, top B m)
  | .list A, m => top A m
  | .arrow A B, m => (m, fun v => top B (m + cost A v))

/-- The least majorant of a type, `ι_A = ⊤_A(0)`. -/
def bot (A : HTy) : Maj A := top A 0

/-! ## The order is a preorder, and the cost function is monotone -/

lemma le_refl : (A : HTy) → (x : Maj A) → le A x x
  | .one, _ => Nat.le_refl _
  | .prod A B, x => ⟨le_refl A x.1, le_refl B x.2⟩
  | .sum A B, x => ⟨le_refl A x.1, le_refl B x.2⟩
  | .list A, x => le_refl A x
  | .arrow _ B, x => ⟨Nat.le_refl _, fun z => le_refl B (x.2 z)⟩

lemma le_trans : (A : HTy) → {x y z : Maj A} → le A x y → le A y z → le A x z
  | .one, _, _, _, h1, h2 => Nat.le_trans h1 h2
  | .prod A B, _, _, _, h1, h2 => ⟨le_trans A h1.1 h2.1, le_trans B h1.2 h2.2⟩
  | .sum A B, _, _, _, h1, h2 => ⟨le_trans A h1.1 h2.1, le_trans B h1.2 h2.2⟩
  | .list A, _, _, _, h1, h2 => le_trans A h1 h2
  | .arrow _ B, _, _, _, h1, h2 =>
      ⟨Nat.le_trans h1.1 h2.1, fun w => le_trans B (h1.2 w) (h2.2 w)⟩

/-- **The cost function is monotone.** -/
lemma cost_mono : (A : HTy) → {x y : Maj A} → le A x y → cost A x ≤ cost A y
  | .one, _, _, h => h
  | .prod A B, _, _, h => max_le_max (cost_mono A h.1) (cost_mono B h.2)
  | .sum A B, _, _, h => max_le_max (cost_mono A h.1) (cost_mono B h.2)
  | .list A, _, _, h => cost_mono A h
  | .arrow _ _, _, _, h => h.1

/-! ## Least upper bounds -/

lemma le_join_left : (A : HTy) → (x y : Maj A) → le A x (join A x y)
  | .one, _, _ => le_max_left _ _
  | .prod A B, x, y => ⟨le_join_left A x.1 y.1, le_join_left B x.2 y.2⟩
  | .sum A B, x, y => ⟨le_join_left A x.1 y.1, le_join_left B x.2 y.2⟩
  | .list A, x, y => le_join_left A x y
  | .arrow _ B, x, y => ⟨le_max_left _ _, fun z => le_join_left B (x.2 z) (y.2 z)⟩

lemma le_join_right : (A : HTy) → (x y : Maj A) → le A y (join A x y)
  | .one, _, _ => le_max_right _ _
  | .prod A B, x, y => ⟨le_join_right A x.1 y.1, le_join_right B x.2 y.2⟩
  | .sum A B, x, y => ⟨le_join_right A x.1 y.1, le_join_right B x.2 y.2⟩
  | .list A, x, y => le_join_right A x y
  | .arrow _ B, x, y => ⟨le_max_right _ _, fun z => le_join_right B (x.2 z) (y.2 z)⟩

lemma join_le : (A : HTy) → {x y z : Maj A} → le A x z → le A y z → le A (join A x y) z
  | .one, _, _, _, h1, h2 => max_le h1 h2
  | .prod A B, _, _, _, h1, h2 => ⟨join_le A h1.1 h2.1, join_le B h1.2 h2.2⟩
  | .sum A B, _, _, _, h1, h2 => ⟨join_le A h1.1 h2.1, join_le B h1.2 h2.2⟩
  | .list A, _, _, _, h1, h2 => join_le A h1 h2
  | .arrow _ B, _, _, _, h1, h2 => ⟨max_le h1.1 h2.1, fun w => join_le B (h1.2 w) (h2.2 w)⟩

lemma isMono_join : (A : HTy) → {x y : Maj A} → IsMono A x → IsMono A y → IsMono A (join A x y)
  | .one, _, _, _, _ => trivial
  | .prod A B, _, _, hx, hy => ⟨isMono_join A hx.1 hy.1, isMono_join B hx.2 hy.2⟩
  | .sum A B, _, _, hx, hy => ⟨isMono_join A hx.1 hy.1, isMono_join B hx.2 hy.2⟩
  | .list A, _, _, hx, hy => isMono_join A hx hy
  | .arrow _ B, _, _, hx, hy =>
      ⟨fun z hz => isMono_join B (hx.1 z hz) (hy.1 z hz),
        fun z w hzw => join_le B (le_trans B (hx.2 z w hzw) (le_join_left B _ _))
          (le_trans B (hy.2 z w hzw) (le_join_right B _ _))⟩

/-! ## Adding a constant -/

/-- **`|μ + r| = |μ| + r`.** -/
lemma cost_add : (A : HTy) → (x : Maj A) → (r : ℕ) → cost A (add A x r) = cost A x + r
  | .one, _, _ => rfl
  | .prod A B, x, r => by
      show max (cost A (add A x.1 r)) (cost B (add B x.2 r))
        = max (cost A x.1) (cost B x.2) + r
      rw [cost_add A x.1 r, cost_add B x.2 r]
      omega
  | .sum A B, x, r => by
      show max (cost A (add A x.1 r)) (cost B (add B x.2 r))
        = max (cost A x.1) (cost B x.2) + r
      rw [cost_add A x.1 r, cost_add B x.2 r]
      omega
  | .list A, x, r => cost_add A x r
  | .arrow _ _, _, _ => rfl

lemma add_mono : (A : HTy) → {x y : Maj A} → le A x y → (r : ℕ) → le A (add A x r) (add A y r)
  | .one, _, _, h, r => Nat.add_le_add_right h r
  | .prod A B, _, _, h, r => ⟨add_mono A h.1 r, add_mono B h.2 r⟩
  | .sum A B, _, _, h, r => ⟨add_mono A h.1 r, add_mono B h.2 r⟩
  | .list A, _, _, h, r => add_mono A h r
  | .arrow _ B, _, _, h, r =>
      ⟨Nat.add_le_add_right h.1 r, fun z => add_mono B (h.2 z) r⟩

lemma isMono_add : (A : HTy) → {x : Maj A} → IsMono A x → (r : ℕ) → IsMono A (add A x r)
  | .one, _, _, _ => trivial
  | .prod A B, _, hx, r => ⟨isMono_add A hx.1 r, isMono_add B hx.2 r⟩
  | .sum A B, _, hx, r => ⟨isMono_add A hx.1 r, isMono_add B hx.2 r⟩
  | .list A, _, hx, r => isMono_add A hx r
  | .arrow _ B, _, hx, r =>
      ⟨fun z hz => isMono_add B (hx.1 z hz) r, fun z w hzw => add_mono B (hx.2 z w hzw) r⟩

/-! ## The majorants `⊤_A(m)` -/

/-- **`|⊤_A(m)| = m`.** -/
lemma cost_top : (A : HTy) → (m : ℕ) → cost A (top A m) = m
  | .one, _ => rfl
  | .prod A B, m => by
      show max (cost A (top A m)) (cost B (top B m)) = m
      rw [cost_top A m, cost_top B m]; omega
  | .sum A B, m => by
      show max (cost A (top A m)) (cost B (top B m)) = m
      rw [cost_top A m, cost_top B m]; omega

  | .list A, m => cost_top A m
  | .arrow _ _, _ => rfl

/-- **`⊤_A(m)` is monotone in `m`.** -/
lemma top_mono : (A : HTy) → {m n : ℕ} → m ≤ n → le A (top A m) (top A n)
  | .one, _, _, h => h
  | .prod A B, _, _, h => ⟨top_mono A h, top_mono B h⟩
  | .sum A B, _, _, h => ⟨top_mono A h, top_mono B h⟩
  | .list A, _, _, h => top_mono A h
  | .arrow _ B, _, _, h => ⟨h, fun _ => top_mono B (Nat.add_le_add_right h _)⟩

/-- **`⊤_A(m)` is a majorant.** -/
lemma isMono_top : (A : HTy) → (m : ℕ) → IsMono A (top A m)
  | .one, _ => trivial
  | .prod A B, m => ⟨isMono_top A m, isMono_top B m⟩
  | .sum A B, m => ⟨isMono_top A m, isMono_top B m⟩
  | .list A, m => isMono_top A m
  | .arrow A B, m =>
      ⟨fun v _ => isMono_top B (m + cost A v),
        fun _ _ hvw => top_mono B (Nat.add_le_add_left (cost_mono A hvw) m)⟩

lemma isMono_bot (A : HTy) : IsMono A (bot A) := isMono_top A 0

lemma cost_bot (A : HTy) : cost A (bot A) = 0 := cost_top A 0

end Maj

end Transducers
