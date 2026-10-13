/-
Exercise `exer:weak-simon-tree-aperiodic` of Part D, Section *Evaluation*
(`partDPolyregular/evaluation.tex`): the values of strings in the monoid `Run N × Cut θ`.

A letter of value `m` is mapped to `thS s θB θO m ∈ Run NB × Cut θO`: in the run component, to
`sv 1 1` if `m = s` and to `ns (θB m)` otherwise; in the cut component, to the one-letter piece
`pc m (m = s) (m = s)`.  This file computes the values of the strings that occur in the
decomposition of the induction step (runs of letters of value `s`, runs of other letters, blocks)
and the information that the ranks read off them (first and last letter, first and last run, the
product of the blocks).
-/
import RequestProject.Exercises.EvalWeakEnc
import RequestProject.Exercises.EvalWeakMon

namespace Transducers.Exercises

open FactTree TreeSym Simon

instance {N : Type} [Finite N] : Finite (Run N) :=
  Finite.of_injective (fun r : Run N => match r with
    | .ns x => (Sum.inl x : N ⊕ (N × N))
    | .sv l t => Sum.inr (l, t)) (by rintro (_ | _) (_ | _) h <;> simp_all)

instance {M NO : Type} [Monoid M] [Monoid NO] {θ : M → NO} [Finite M] [Finite NO] :
    Finite (Cut θ) :=
  Finite.of_injective (fun c : Cut θ => match c with
    | .e => (Sum.inl none : Option (M × Bool × Bool) ⊕ (Bool × M × NO × M × Bool))
    | .pc m f l => Sum.inl (some (m, f, l))
    | .ct f a x b l => Sum.inr (f, a, x, b, l)) (by rintro (_ | _ | _) (_ | _ | _) h <;> simp_all)

lemma val_pair {X N N' : Type} [Monoid N] [Monoid N'] (f : X → N) (g : X → N') (u : List X) :
    val (fun x => (f x, g x)) u = (val f u, val g u) := by
  induction u with
  | nil => rfl
  | cons x u ih => rw [val_cons, ih, val_cons, val_cons]; rfl

section Values

variable {M : Type} [Monoid M] [DecidableEq M] (s : M) {NB NO : Type} [Monoid NB] [Monoid NO]
  (θB : M → NB) (θO : M → NO)

/-- The run component of the image of a letter value. -/
def thR (m : M) : Run NB := if m = s then Run.sv 1 1 else Run.ns (θB m)

/-- The cut component of the image of a letter value. -/
def thC (m : M) : Cut θO := Cut.pc m (decide (m = s)) (decide (m = s))

/-- The image of a letter value in `Run NB × Cut θO`. -/
def thS (m : M) : Run NB × Cut θO := (thR s θB m, thC s θO m)

variable {X : Type} (φ : X → M)

lemma val_thS (u : List X) :
    val (thS s θB θO ∘ φ) u = (val (thR s θB ∘ φ) u, val (thC s θO ∘ φ) u) :=
  val_pair (fun x => thR s θB (φ x)) (fun x => thC s θO (φ x)) u

omit [Monoid M] in
lemma valR_ns : ∀ u : List X, (∀ x ∈ u, φ x ≠ s) →
    val (thR s θB ∘ φ) u = Run.ns (val (θB ∘ φ) u)
  | [], _ => rfl
  | x :: u, h => by
    rw [val_cons, valR_ns u fun y hy => h y (by simp [hy]), val_cons]
    simp [thR, h x (by simp)]

omit [Monoid M] in
lemma valR_s : ∀ u : List X, u ≠ [] → (∀ x ∈ u, φ x = s) → val (thR s θB ∘ φ) u = Run.sv 1 1
  | [], h, _ => absurd rfl h
  | [x], _, h => by simp [thR, h x (by simp)]
  | x :: y :: u, _, h => by
    rw [val_cons, valR_s (y :: u) (by simp) fun z hz => h z (by simp [hz])]
    simp [thR, h x (by simp)]

lemma valC_ns : ∀ u : List X, u ≠ [] → (∀ x ∈ u, φ x ≠ s) →
    val (thC s θO ∘ φ) u = Cut.pc (val φ u) false false
  | [], h, _ => absurd rfl h
  | [x], _, h => by simp [thC, h x (by simp)]
  | x :: y :: u, _, h => by
    rw [val_cons, valC_ns (y :: u) (by simp) fun z hz => h z (by simp [hz])]
    simp [thC, h x (by simp), Cut.pc_mul_pc]

lemma valC_s : ∀ u : List X, u ≠ [] → (∀ x ∈ u, φ x = s) →
    val (thC s θO ∘ φ) u = Cut.pc (val φ u) true true
  | [], h, _ => absurd rfl h
  | [x], _, h => by simp [thC, h x (by simp)]
  | x :: y :: u, _, h => by
    rw [val_cons, valC_s (y :: u) (by simp) fun z hz => h z (by simp [hz])]
    simp [thC, h x (by simp), Cut.pc_mul_pc]

/-- A block: a nonempty run of letters of other values than `s`, followed by a nonempty run of
letters of value `s`. -/
def IsBlock (y : List X) : Prop :=
  ∃ b c, y = b ++ c ∧ b ≠ [] ∧ c ≠ [] ∧ (∀ x ∈ b, φ x ≠ s) ∧ ∀ x ∈ c, φ x = s

lemma valC_block {y : List X} (hy : IsBlock s φ y) :
    val (thC s θO ∘ φ) y = Cut.pc (val φ y) false true := by
  obtain ⟨b, c, rfl, hb, hc, hbs, hcs⟩ := hy
  rw [val_append, valC_ns s θO φ b hb hbs, valC_s s θO φ c hc hcs, Cut.pc_mul_pc]
  simp

/-- The string is empty or ends with a letter of value `s`. -/
def EndsS (u : List X) : Prop := u = [] ∨ ∃ u' x, u = u' ++ [x] ∧ φ x = s

/-- The string is empty or starts with a letter of another value than `s`. -/
def StartsNS (u : List X) : Prop := u = [] ∨ ∃ x u', u = x :: u' ∧ φ x ≠ s

omit [Monoid M] [DecidableEq M] in
lemma EndsS.append {u v : List X} (hu : EndsS s φ u) (hv : EndsS s φ v) :
    EndsS s φ (u ++ v) := by
  rcases hv with rfl | ⟨v', x, rfl, hx⟩
  · simpa using hu
  · exact Or.inr ⟨u ++ v', x, by simp, hx⟩

omit [Monoid M] [DecidableEq M] in
lemma EndsS.flatten : ∀ {l : List (List X)}, (∀ y ∈ l, EndsS s φ y) → EndsS s φ l.flatten
  | [], _ => Or.inl rfl
  | y :: l, h => by
    rw [List.flatten_cons]
    exact (h y (by simp)).append s φ (EndsS.flatten fun z hz => h z (by simp [hz]))

omit [Monoid M] [DecidableEq M] in
lemma StartsNS.append {u v : List X} (hu : StartsNS s φ u) (hv : StartsNS s φ v) :
    StartsNS s φ (u ++ v) := by
  rcases hu with rfl | ⟨x, u', rfl, hx⟩
  · simpa using hv
  · exact Or.inr ⟨x, u' ++ v, by simp, hx⟩

omit [Monoid M] [DecidableEq M] in
lemma StartsNS.flatten : ∀ {l : List (List X)}, (∀ y ∈ l, StartsNS s φ y) →
    StartsNS s φ l.flatten
  | [], _ => Or.inl rfl
  | y :: l, h => by
    rw [List.flatten_cons]
    exact (h y (by simp)).append s φ (StartsNS.flatten fun z hz => h z (by simp [hz]))

omit [Monoid M] [DecidableEq M] in
lemma IsBlock.endsS {y : List X} (h : IsBlock s φ y) : EndsS s φ y := by
  obtain ⟨b, c, rfl, -, hc, -, hcs⟩ := h
  obtain ⟨c', x, rfl⟩ := (List.eq_nil_or_concat c).resolve_left hc
  exact Or.inr ⟨b ++ c', x, by simp, hcs x (by simp)⟩

omit [Monoid M] [DecidableEq M] in
lemma IsBlock.startsNS {y : List X} (h : IsBlock s φ y) : StartsNS s φ y := by
  obtain ⟨b, c, rfl, hb, -, hbs, -⟩ := h
  obtain ⟨x, b', rfl⟩ := List.exists_cons_of_ne_nil hb
  exact Or.inr ⟨x, b' ++ c, by simp, hbs x (by simp)⟩

omit [Monoid M] [DecidableEq M] in
lemma endsS_of_all_s {u : List X} (h : ∀ x ∈ u, φ x = s) : EndsS s φ u := by
  rcases List.eq_nil_or_concat u with rfl | ⟨u', x, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨u', x, by simp, h x (by simp)⟩

omit [Monoid M] [DecidableEq M] in
lemma startsNS_of_all_ns {u : List X} (h : ∀ x ∈ u, φ x ≠ s) : StartsNS s φ u := by
  rcases u with _ | ⟨x, u'⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨x, u', rfl, h x (by simp)⟩

/-- The context on the left of a string that is empty or ends with `s`. -/
lemma ctxL {u : List X} (h : EndsS s φ u) :
    Run.trail (val (thR s θB ∘ φ) u) = 1 ∧
      (val (thC s θO ∘ φ) u = Cut.e ∨ Cut.lastS (val (thC s θO ∘ φ) u) = true) := by
  rcases h with rfl | ⟨u', x, rfl, hx⟩
  · exact ⟨rfl, Or.inl rfl⟩
  · simp only [val_append, val_singleton, Function.comp_apply, thR, thC, hx, if_true,
      decide_true]
    exact ⟨Run.trail_mul_sv _ _ _, Or.inr (Cut.lastS_mul_pc _ _ _ _)⟩

/-- The context on the right of a string that is empty or starts with another value than `s`. -/
lemma ctxR {u : List X} (h : StartsNS s φ u) :
    val (thC s θO ∘ φ) u = Cut.e ∨ Cut.firstS (val (thC s θO ∘ φ) u) = false := by
  rcases h with rfl | ⟨x, u', rfl, hx⟩
  · exact Or.inl rfl
  · simp only [val_cons, Function.comp_apply, thC, hx, decide_false]
    exact Or.inr (Cut.firstS_pc_mul _ _ _ _)

omit [Monoid M] in
lemma lead_startsS {u : List X} {x : X} (hx : φ x = s) (α : Run NB) :
    Run.lead (val (thR s θB ∘ φ) (x :: u) * α) = 1 := by
  rw [val_cons]
  simp only [Function.comp_apply, thR, hx, if_true, mul_assoc]
  exact Run.lead_sv_mul _ _ _

lemma lastS_last (α : Cut θO) (u : List X) (x : X) :
    Cut.lastS (α * val (thC s θO ∘ φ) (u ++ [x])) = decide (φ x = s) := by
  rw [val_append, val_singleton, ← mul_assoc]
  exact Cut.lastS_mul_pc _ _ _ _

lemma firstS_first (β : Cut θO) (u : List X) (x : X) :
    Cut.firstS (val (thC s θO ∘ φ) (x :: u) * β) = decide (φ x = s) := by
  rw [val_cons, mul_assoc]
  exact Cut.firstS_pc_mul _ _ _ _

omit [Monoid M] in
lemma hasS_of_mem : ∀ {u : List X}, (∃ x ∈ u, φ x = s) → Run.hasS (val (thR s θB ∘ φ) u) = true
  | [], ⟨x, hx, _⟩ => by simp at hx
  | y :: u, ⟨x, hx, hxs⟩ => by
    rw [val_cons, Run.hasS_mul]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [thR, hxs, Run.hasS]
    · rw [hasS_of_mem ⟨x, hx, hxs⟩]; simp

omit [Monoid M] in
lemma hasS_of_all_ns {u : List X} (h : ∀ x ∈ u, φ x ≠ s) :
    Run.hasS (val (thR s θB ∘ φ) u) = false := by
  rw [valR_ns s θB φ u h]; rfl

/-- The product of the blocks, read from the left. -/
lemma blocksL_blocks : ∀ (pre : List (List X)) (α : Cut θO), (α = Cut.e ∨ Cut.lastS α = true) →
    (∀ y ∈ pre, IsBlock s φ y) →
    Cut.blocksL (α * val (thC s θO ∘ φ) pre.flatten) =
        Cut.blocksL α * val (θO ∘ val φ) pre ∧
      (pre ≠ [] → Cut.lastS (α * val (thC s θO ∘ φ) pre.flatten) = true ∧
        Cut.hasNS (α * val (thC s θO ∘ φ) pre.flatten) = true)
  | [], α, _, _ => by simp
  | y :: pre, α, hα, hb => by
    have h1 := Cut.blocksL_mul_block hα (val φ y)
    rw [List.flatten_cons, val_append, valC_block s θO φ (hb y (by simp)), ← mul_assoc]
    obtain ⟨h2, h3⟩ := blocksL_blocks pre (α * Cut.pc (val φ y) false true) (Or.inr h1.2.1)
      fun z hz => hb z (by simp [hz])
    refine ⟨by rw [h2, h1.1, val_cons, mul_assoc]; rfl, fun _ => ?_⟩
    rcases eq_or_ne pre [] with rfl | hpre
    · simpa using h1.2
    · exact h3 hpre

/-- The product of the blocks, read from the right. -/
lemma blocksR_blocks : ∀ (post : List (List X)) (β : Cut θO),
    (β = Cut.e ∨ Cut.firstS β = false) → (∀ y ∈ post, IsBlock s φ y) →
    Cut.blocksR (val (thC s θO ∘ φ) post.flatten * β) =
        val (θO ∘ val φ) post * Cut.blocksR β ∧
      (val (thC s θO ∘ φ) post.flatten * β = Cut.e ∨
        Cut.firstS (val (thC s θO ∘ φ) post.flatten * β) = false)
  | [], β, hβ, _ => by simpa using hβ
  | y :: post, β, hβ, hb => by
    obtain ⟨h2, h3⟩ := blocksR_blocks post β hβ fun z hz => hb z (by simp [hz])
    have h1 := Cut.blocksR_block_mul h3 (val φ y)
    rw [List.flatten_cons, val_append, valC_block s θO φ (hb y (by simp)), mul_assoc]
    refine ⟨by rw [h1.1, h2, val_cons, mul_assoc]; rfl, Or.inr h1.2⟩

lemma blocksL_allS {u : List X} (h : ∀ x ∈ u, φ x = s) :
    Cut.blocksL (val (thC s θO ∘ φ) u) = 1 ∧ (val (thC s θO ∘ φ) u = Cut.e ∨
      Cut.lastS (val (thC s θO ∘ φ) u) = true) ∧ Cut.hasNS (val (thC s θO ∘ φ) u) = false := by
  rcases eq_or_ne u [] with rfl | hu
  · exact ⟨rfl, Or.inl rfl, rfl⟩
  · rw [valC_s s θO φ u hu h]
    exact ⟨rfl, Or.inr rfl, rfl⟩

lemma blocksR_allNS {u : List X} (h : ∀ x ∈ u, φ x ≠ s) :
    Cut.blocksR (val (thC s θO ∘ φ) u) = 1 := by
  rcases eq_or_ne u [] with rfl | hu
  · rfl
  · rw [valC_ns s θO φ u hu h]; rfl

end Values

end Transducers.Exercises
