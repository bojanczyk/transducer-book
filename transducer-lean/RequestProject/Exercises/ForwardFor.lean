/-
Exercise `exer:forward-for-transducer` of the chapter *For-transducers*
(`polyregular-for.tex`) of *Transducers* (M. Bojańczyk) -- the definitions and the two
constructions of the easy inclusion.

A *forward* for-transducer is a for-transducer all of whose loops are of the first-to-last kind.
This file introduces the syntactic predicate `Transducers.Exercises.ForwardProg` saying so, the
class `Transducers.Exercises.IsForwardFor` of the functions computed by such programs, and proves
two of the three things the author's solution needs for the inclusion from right to left:

* marked squaring is computed by a forward for-transducer (the program is the one of
  Example `ex:marked-squaring-for-transducer`, already used for Theorem
  `thm:for-transducers-are-polyregular`, whose two loops are forward);
* every rational function is computed by a forward for-transducer.

The second one is where the author's remark is used: a rational function is computed by a
bimachine (Theorem `thm:bimachines`), and the bimachine may be run with its suffix automaton
going *forwards*.  The project's simulation of a bimachine by a for-transducer
(`Transducers.bimProg`) runs the suffix automaton backwards over the suffix, in an inner loop of
the last-to-first kind; the simulation below replaces that inner loop by a forward one whose
state is the *transition map* `S → S` of the suffix automaton on the part of the suffix read so
far, composed on the right, so that the map obtained at the end of the inner loop, applied to the
initial state, is exactly the state of the suffix automaton on the suffix.  This is the standard
way of running a right-to-left automaton from left to right, and it is what the author means by
"the suffix automaton is run on the suffix in the forward direction, since the only role of the
suffix automaton is to split the suffixes into finitely many regular languages".

The third thing -- closure of forward for-transducers under composition -- and the inclusion from
left to right are in `RequestProject/Exercises/ForwardForTop.lean`.
-/
import RequestProject.PartD.ForPrimes

namespace Transducers
namespace Exercises

/-! ## Forward for-transducers -/

/-- A for-program is *forward* when every one of its loops is of the first-to-last kind. -/
def ForwardProg {A B : Type} : ForProg A B → Prop
  | ForProg.skip => True
  | ForProg.output _ => True
  | ForProg.assign _ _ => True
  | ForProg.seq P Q => ForwardProg P ∧ ForwardProg Q
  | ForProg.ite _ P Q => ForwardProg P ∧ ForwardProg Q
  | ForProg.loop d _ P => d = true ∧ ForwardProg P

/-- **A forward for-transducer**: a function computed by a for-program all of whose loops are of
the first-to-last kind. -/
def IsForwardFor {A B : Type} (f : List A → List B) : Prop :=
  ∃ P : ForProg A B, ForwardProg P ∧ ∀ w, P.eval w = f w

variable {A B C Q : Type}

lemma IsForwardFor.congr {f g : List A → List B} (hf : IsForwardFor f) (h : ∀ w, f w = g w) :
    IsForwardFor g := by
  obtain ⟨P, hP, hPe⟩ := hf
  exact ⟨P, hP, fun w => (hPe w).trans (h w)⟩

/-- A loop-free program is forward. -/
lemma forwardProg_of_loopFree : ∀ {P : ForProg A B}, P.LoopFree → ForwardProg P
  | ForProg.skip, _ => trivial
  | ForProg.output _, _ => trivial
  | ForProg.assign _ _, _ => trivial
  | ForProg.seq _ _, h => ⟨forwardProg_of_loopFree h.1, forwardProg_of_loopFree h.2⟩
  | ForProg.ite _ _ _, h => ⟨forwardProg_of_loopFree h.1, forwardProg_of_loopFree h.2⟩

/-! ## Forward machine programs -/

/-- A machine program is *forward* when every one of its loops is of the first-to-last kind. -/
def ForwardMProg {A B Q : Type} : MProg A B Q → Prop
  | MProg.act _ => True
  | MProg.act2 _ _ _ => True
  | MProg.seq P R => ForwardMProg P ∧ ForwardMProg R
  | MProg.loop d _ P => d = true ∧ ForwardMProg P

lemma loopFree_constProg : ∀ l : List B, (constProg l : ForProg A B).LoopFree
  | [] => trivial
  | _ :: l => ⟨trivial, loopFree_constProg l⟩

lemma loopFree_setStateAux {q₀ : Q} (E : BoolEnc Q q₀) (q : Q) :
    ∀ k : ℕ, (E.setStateAux (A := A) (B := B) q k).LoopFree
  | 0 => trivial
  | k + 1 => ⟨loopFree_setStateAux E q k, trivial⟩

lemma loopFree_setState {q₀ : Q} (E : BoolEnc Q q₀) (q : Q) :
    (E.setState (A := A) (B := B) q).LoopFree := loopFree_setStateAux E q E.n

lemma loopFree_casesBy {ι : Type} (test : ι → ForTest A) (body : ι → ForProg A B)
    (hbody : ∀ i, (body i).LoopFree) : ∀ l : List ι, (casesBy test body l).LoopFree
  | [] => trivial
  | i :: l => ⟨hbody i, loopFree_casesBy test body hbody l⟩

/-- Compiling a forward machine program gives a forward for-program: the compilation of an
action is loop-free, and a loop keeps its direction. -/
lemma forwardProg_compile {q₀ : Q} (E : BoolEnc Q q₀) (as : List A) (qs : List Q) :
    ∀ M : MProg A B Q, ForwardMProg M → ForwardProg (M.compile E as qs) := by
  intro M
  induction M with
  | act f =>
      intro _
      apply forwardProg_of_loopFree
      apply loopFree_casesBy
      intro q
      exact ⟨loopFree_constProg _, loopFree_setState E _⟩
  | act2 x y f =>
      intro _
      apply forwardProg_of_loopFree
      apply loopFree_casesBy
      intro z
      exact ⟨loopFree_constProg _, loopFree_setState E _⟩
  | seq P R ihP ihR => intro h; exact ⟨ihP h.1, ihR h.2⟩
  | loop d x P ih => intro h; exact ⟨h.1, ih h.2⟩

/-- **A function computed by a forward machine program is computed by a forward
for-transducer.** -/
theorem isForwardFor_of_mprog [Finite A] [Finite Q] (M : MProg A B Q) (hM : ForwardMProg M)
    (q₀ : Q) (f : List A → List B) (h : ∀ w, (M.sem w (fun _ => 0) q₀).2 = f w) :
    IsForwardFor f := by
  classical
  obtain ⟨E⟩ := nonempty_boolEnc q₀
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype Q := Fintype.ofFinite Q
  refine ⟨M.compile E (Finset.univ : Finset A).toList (Finset.univ : Finset Q).toList,
    forwardProg_compile E _ _ M hM, ?_⟩
  intro w
  have h0 : (fun _ => false : ℕ → Bool) = E.repOf q₀ (fun _ => false) := E.repOf_init.symm
  rw [ForProg.eval, h0,
    exec_compile (fun a => by simp) (fun q => by simp) w M (fun _ => 0) (fun _ => false) q₀]
  exact h w

/-! ## Marked squaring -/

/-- **Marked squaring is computed by a forward for-transducer**: the two loops of the program
`Transducers.msProg` of Example `ex:marked-squaring-for-transducer` are both forward. -/
theorem isForwardFor_markedSquare (A : Type) [Finite A] : IsForwardFor (markedSquare A) :=
  isForwardFor_of_mprog (msProg A) ⟨rfl, rfl, trivial⟩ () _ (fun w => sem_msProg A w _)

/-! ## Rational functions

A bimachine is simulated by a forward machine program: the inner loop, which computes the state
of the suffix automaton, is forward, and its state is the transition map of the suffix automaton
on the part of the suffix read so far. -/

section Bimach

variable {P S : Type}

/-- The transition map of the suffix automaton on the suffix starting at `i`, read from right to
left; the state of the suffix automaton at the gap before `i` is its value at the initial
state. -/
def bimSufFun (M : Bimachine A B P S) (w : List A) (i : ℕ) : S → S :=
  fun s => strTrans M.suffixStep (w.drop i).reverse s

lemma bimSufFun_init (M : Bimachine A B P S) (w : List A) (i : ℕ) :
    bimSufFun M w i M.suffixInit = bimSuf M w i := rfl

/-- **A forward loop computes the transition map of a right-to-left automaton.**  The loop runs
over the positions of the input from the first to the last, and composes, on the right, the
transition of every position at least `x`. -/
lemma runList_fwd_suffix {S : Type} (step : S → A → S) (w : List A) (x : ℕ) :
    ∀ (n : ℕ), n ≤ w.length → ∀ H : S → S,
      runList (fun (H' : S → S) (p : ℕ) =>
          ((if x ≤ p then (fun s => H' ((w[p]?).elim s (fun a => step s a))) else H'),
            ([] : List B)))
        (List.range n) H
        = ((fun s => H (strTrans step ((w.take n).drop x).reverse s)), []) := by
  intro n
  induction n with
  | zero => intro _ H; simp [strTrans]
  | succ n ih =>
      intro hn H
      have hnw : n < w.length := by omega
      have hsucc : w.take (n + 1) = w.take n ++ [w[n]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hnw]; rfl
      rw [List.range_succ, runList_append, ih (by omega)]
      simp only [runList_cons, runList_nil, List.append_nil]
      refine Prod.ext ?_ rfl
      by_cases hx : x ≤ n
      · have hd : (w.take (n + 1)).drop x = (w.take n).drop x ++ [w[n]] := by
          rw [hsucc, List.drop_append_of_le_length (by simp; omega)]
        simp only [if_pos hx, hd, List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append, List.getElem?_eq_getElem hnw, Option.elim_some]
        funext s
        rw [strTrans, strTrans, List.foldl_cons]
      · have h1 : (w.take (n + 1)).drop x = [] := by
          refine List.drop_eq_nil_of_le ?_
          have : (w.take (n + 1)).length ≤ n + 1 := by simp
          omega
        have h2 : (w.take n).drop x = [] := by
          refine List.drop_eq_nil_of_le ?_
          have : (w.take n).length ≤ n := by simp
          omega
        simp only [if_neg hx, h1, h2]

/-- The body of the outer loop of the forward simulation of a bimachine: the transition map of
the suffix automaton is reset and computed by a *forward* inner loop over the positions at least
the current one, then the output at the current gap is emitted and the prefix automaton
advances. -/
def bimBodyF (M : Bimachine A B P S) : MProg A B (P × (S → S)) :=
  MProg.seq (MProg.act (fun q => ((q.1, id), [])))
    (MProg.seq
      (MProg.loop true 1 (MProg.act2 1 0 (fun q oa _ _ c₂ =>
        ((q.1, if c₂ then (fun s => q.2 (oa.elim s (fun a => M.suffixStep s a))) else q.2), []))))
      (MProg.act2 0 0 (fun q oa _ _ _ =>
        ((oa.elim q.1 (fun a => M.prefixStep q.1 a), q.2), M.out q.1 (q.2 M.suffixInit)))))

/-- The forward machine program computing a bimachine. -/
def bimProgF (M : Bimachine A B P S) : MProg A B (P × (S → S)) :=
  MProg.seq (MProg.loop true 0 (bimBodyF M))
    (MProg.act (fun q => (q, M.out q.1 M.suffixInit)))

lemma forwardMProg_bimProgF (M : Bimachine A B P S) : ForwardMProg (bimProgF M) :=
  ⟨⟨rfl, trivial, ⟨rfl, trivial⟩, trivial⟩, trivial⟩

lemma sem_bimBodyF (M : Bimachine A B P S) (w : List A) (pos : ℕ → ℕ) (i : ℕ)
    (q : P × (S → S)) :
    MProg.sem w (bimBodyF M) (Function.update pos 0 i) q
      = (((bimStep M w q.1 i).1, bimSufFun M w i), (bimStep M w q.1 i).2) := by
  have hupd0 : ∀ p : ℕ, (Function.update (Function.update pos 0 i) 1 p) 0 = i := by
    intro p
    rw [Function.update_of_ne (by decide), Function.update_self]
  have hupd1 : ∀ p : ℕ, (Function.update (Function.update pos 0 i) 1 p) 1 = p := by
    intro p; rw [Function.update_self]
  rw [bimBodyF]
  simp only [MProg.sem_seq, MProg.sem_act, MProg.sem_loop, MProg.sem_act2, loopRange_true,
    hupd0, hupd1, decide_eq_true_eq]
  have hinner : runList (fun (q' : P × (S → S)) (p : ℕ) =>
        ((q'.1, if i ≤ p then (fun s => q'.2 ((w[p]?).elim s (fun a => M.suffixStep s a)))
          else q'.2), ([] : List B)))
      (List.range w.length) (q.1, id)
      = ((q.1, bimSufFun M w i), []) := by
    rw [runList_pair_snd (f := fun (H : S → S) (p : ℕ) =>
      ((if i ≤ p then (fun s => H ((w[p]?).elim s (fun a => M.suffixStep s a))) else H),
        ([] : List B)))]
    rw [runList_fwd_suffix M.suffixStep w i w.length le_rfl]
    simp only [List.take_length]
    rfl
  rw [hinner]
  simp only [Function.update_self, bimStep, List.nil_append, bimSufFun_init]

lemma sem_bimProgF (M : Bimachine A B P S) (w : List A) (pos : ℕ → ℕ) :
    ((bimProgF M).sem w pos (M.prefixInit, id)).2 = M.eval w := by
  have hstep : (fun (q : P × (S → S)) (p : ℕ) =>
        MProg.sem w (bimBodyF M) (Function.update pos 0 p) q)
      = (fun (q : P × (S → S)) (i : ℕ) =>
          (((bimStep M w q.1 i).1, bimSufFun M w i), (bimStep M w q.1 i).2)) :=
    funext fun q => funext fun i => sem_bimBodyF M w pos i q
  rw [bimProgF, MProg.sem_seq, MProg.sem_loop, loopRange_true, hstep]
  obtain ⟨h1, h2⟩ := runList_pair_fst (bimStep M w) (fun (_ : P) (i : ℕ) => bimSufFun M w i)
    (List.range w.length) M.prefixInit id
  simp only [MProg.sem_act]
  rw [h1, h2]
  have hbs : bimStep M w
      = fun (p : P) (i : ℕ) =>
          ((w[i]?).elim p (fun a => M.prefixStep p a), M.out p (bimSuf M w i)) := rfl
  rw [hbs, runList_range_scan M.prefixStep (fun p i => M.out p (bimSuf M w i)) w w.length le_rfl]
  rw [Bimachine.eval, List.range_succ]
  simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.take_length, bimSuf,
    List.drop_length, List.reverse_nil, strTrans, List.foldl_nil]

/-- **A bimachine is simulated by a forward for-transducer.** -/
theorem isForwardFor_of_isBimachine [Finite A] {f : List A → List B} (hf : IsBimachine f) :
    IsForwardFor f := by
  obtain ⟨P, S, hP, hS, M, hM⟩ := hf
  haveI := hP
  haveI := hS
  exact isForwardFor_of_mprog (bimProgF M) (forwardMProg_bimProgF M) (M.prefixInit, id) f
    (fun w => by rw [sem_bimProgF M w]; exact congrFun hM w)

end Bimach

/-- **A rational function is computed by a forward for-transducer.**  This is the second of the
three ingredients of the author's solution of `exer:forward-for-transducer`. -/
theorem isForwardFor_of_isRationalFun [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) : IsForwardFor f :=
  isForwardFor_of_isBimachine (isBimachine_of_rationalFun hf)

end Exercises
end Transducers
