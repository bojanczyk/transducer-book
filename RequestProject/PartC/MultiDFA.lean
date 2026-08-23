/-
One deterministic automaton for a finite family of regular languages.

The walking transducer of Theorem C.4.8 runs, on the infix between the current
position and the position it is walking towards, an automaton for each of the
finitely many binary questions it may ask.  Running them all at once is the
usual product construction: a single deterministic transition function whose
state space is the product of the state spaces, with one acceptance condition
per question.  This is what `MultiDFA.exists_prod` provides.

The file also contains the regular language "the last letter belongs to `F`",
used for the question "which is the first element of the output order?", whose
answer only depends on the last letter of the prefix scanned so far.
-/
import RequestProject.PartC.RegAut

namespace Transducers

namespace MultiDFA

variable {Γ R : Type}

/-- One deterministic automaton for a finite family of regular languages. -/
theorem exists_prod [Finite R] (Lang : R → Language Γ) (h : ∀ r, (Lang r).IsRegular) :
    ∃ (S : Type) (_ : Finite S) (step : S → Γ → S) (s0 : S) (acc : R → Set S),
      ∀ (r : R) (u : List Γ), (u.foldl step s0 ∈ acc r ↔ u ∈ Lang r) := by
  classical
  choose σ hσ M hM using h
  haveI : ∀ r, Finite (σ r) := fun r => @Finite.of_fintype _ (hσ r)
  refine ⟨∀ r, σ r, inferInstance, fun s c r => (M r).step (s r) c, fun r => (M r).start,
    fun r => {s | s r ∈ (M r).accept}, ?_⟩
  intro r u
  have key : ∀ (u : List Γ) (s : ∀ r, σ r),
      (u.foldl (fun s c r => (M r).step (s r) c) s) r = u.foldl (M r).step (s r) := by
    intro u
    induction u with
    | nil => intro s; rfl
    | cons c u ih => intro s; exact ih _
  rw [Set.mem_setOf_eq, key, ← hM r, DFA.mem_accepts]
  rfl

/-! ## The last letter -/

/-- The state of the automaton that remembers the last letter read. -/
lemma foldl_last (u : List Γ) (o : Option Γ) :
    u.foldl (fun (_ : Option Γ) c => some c) o = if u = [] then o else u.getLast? := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, List.getLast?_concat, List.append_eq_nil_iff,
        List.cons_ne_self, and_false, if_false]

/-- The language of the strings whose last letter belongs to `F`. -/
lemma isRegular_last [Finite Γ] (F : Set Γ) :
    Language.IsRegular {u : List Γ | ∃ c, u.getLast? = some c ∧ c ∈ F} := by
  have h := RegAut.isRegular_foldl (Γ := Γ) (fun (_ : Option Γ) c => some c) none
    {o : Option Γ | ∃ c, o = some c ∧ c ∈ F}
  refine RegAut.isRegular_of_eq h (fun u => ?_)
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, foldl_last]
  by_cases hu : u = []
  · subst hu; simp
  · rw [if_neg hu, Set.mem_setOf_eq]

end MultiDFA

end Transducers
