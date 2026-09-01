/-
Exercise `exer:forward-for-transducer` of the chapter *For-transducers*
(`polyregular-for.tex`) of *Transducers* (M. Bojańczyk) -- **forward for-transducers are closed
under composition**.

This is Lemma `lem:for-closed-under-composition` with the direction of every loop tracked.  The
composed program is `Transducers.compProgAt` of `RequestProject/PartD/ForCompTop.lean`; it is built
from the nest of loops of the inner for-transducer and from the outer program, and none of the
pieces of the construction introduces a last-to-first loop:

* the two length flags are raised by `Transducers.lenProg`, a first-to-last loop;
* the loops of the translation `Transducers.tr` of the outer program are those of the nest of the
  inner one (`Transducers.loopNest`) and those of the re-simulation `Transducers.resim`, which are
  again the loops of the nest;
* the closure `Transducers.closeProg` of the atomised outer program binds its free position
  variables with `Transducers.firstOnly`, a first-to-last loop, and atomising a program does not
  change its loops;
* the branch for the inputs of at most one letter is loop-free.

So the only last-to-first loop the construction of the book uses is the one of the nest form
`Transducers.for_nest_form`, and the forward nest form of
`RequestProject/Exercises/ForwardPrenex.lean` removes it.
-/
import RequestProject.Exercises.ForwardPrenex
import RequestProject.PartD.ForPolyreg

namespace Transducers
namespace Exercises

open scoped Classical

variable {A B C : Type}

/-! ## Loop-freeness of the auxiliary programs -/

lemma loopFree_clearBools : ∀ l : List ℕ, (clearBools l : ForProg A C).LoopFree
  | [] => trivial
  | _ :: l => ⟨trivial, loopFree_clearBools l⟩

lemma loopFree_markOut (fl : ℕ) (q : B → Bool) :
    ∀ {P : ForProg A B}, P.LoopFree → (markOut fl q P : ForProg A C).LoopFree
  | ForProg.skip, _ => trivial
  | ForProg.output _, _ => trivial
  | ForProg.assign _ _, _ => trivial
  | ForProg.seq _ _, h => ⟨loopFree_markOut fl q h.1, loopFree_markOut fl q h.2⟩
  | ForProg.ite _ _ _, h => ⟨loopFree_markOut fl q h.1, loopFree_markOut fl q h.2⟩

lemma loopFree_cpsFree : ∀ (R : ForProg A B), R.LoopFree →
    ∀ k : List B → ForProg A C, (∀ v, (k v).LoopFree) → (cpsFree R k).LoopFree := by
  intro R
  induction R with
  | skip => intro _ k hk; exact hk []
  | output b => intro _ k hk; exact hk [b]
  | assign i v => intro _ k hk; exact ⟨trivial, hk []⟩
  | seq R S ihR ihS =>
      intro h k hk
      exact ihR h.1 _ (fun u => ihS h.2 _ (fun v => hk (u ++ v)))
  | ite t R S ihR ihS => intro h k hk; exact ⟨ihR h.1 k hk, ihS h.2 k hk⟩
  | loop d x R _ => intro h; exact absurd h (by exact fun hc => hc)

/-! ## Forwardness of the pieces of the construction -/

lemma forwardProg_nestLoops : ∀ (L : List (Bool × ℕ)) (body : ForProg A B),
    (∀ q ∈ L, q.1 = true) → ForwardProg body → ForwardProg (ForProg.nestLoops L body)
  | [], body, _, hb => hb
  | (d, x) :: L, body, hL, hb =>
      ⟨hL (d, x) (by simp), forwardProg_nestLoops L body (fun q hq => hL q (by simp [hq])) hb⟩

lemma forwardProg_lenProg (X Y : ℕ) : ForwardProg (lenProg X Y : ForProg A C) :=
  ⟨rfl, trivial, trivial⟩

lemma forwardProg_iteAtom : ∀ (t : ForTest A) (P R : ForProg A B), ForwardProg P → ForwardProg R →
    ForwardProg (ForProg.iteAtom t P R) := by
  intro t
  induction t with
  | boolVar i => exact fun P R hP hR => ⟨hP, hR⟩
  | eqPos i j => exact fun P R hP hR => ⟨hP, hR⟩
  | lePos i j => exact fun P R hP hR => ⟨hP, hR⟩
  | label i a => exact fun P R hP hR => ⟨hP, hR⟩
  | not t ih => exact fun P R hP hR => ih R P hR hP
  | and t s iht ihs => exact fun P R hP hR => iht _ R (ihs P R hP hR) hR
  | or t s iht ihs => exact fun P R hP hR => iht P _ hP (ihs P R hP hR)

lemma forwardProg_atomize : ∀ P : ForProg A B, ForwardProg P → ForwardProg (ForProg.atomize P)
  | ForProg.skip, _ => trivial
  | ForProg.output _, _ => trivial
  | ForProg.assign _ _, _ => trivial
  | ForProg.seq P Q, h => ⟨forwardProg_atomize P h.1, forwardProg_atomize Q h.2⟩
  | ForProg.ite t P Q, h =>
      forwardProg_iteAtom t _ _ (forwardProg_atomize P h.1) (forwardProg_atomize Q h.2)
  | ForProg.loop _ _ P, h => ⟨h.1, forwardProg_atomize P h.2⟩

lemma forwardProg_firstOnly (X y : ℕ) (P : ForProg A B) (h : ForwardProg P) :
    ForwardProg (firstOnly X y P) :=
  ⟨trivial, rfl, ⟨h, trivial⟩, trivial⟩

lemma forwardProg_bindVars : ∀ (ys : List ℕ) (F : ℕ) (P : ForProg A B), ForwardProg P →
    ForwardProg (bindVars F ys P)
  | [], _, _, h => h
  | _ :: ys, F, P, h => forwardProg_firstOnly _ _ _ (forwardProg_bindVars ys (F + 1) P h)

lemma forwardProg_closeProg (E F : ℕ) (Q : ForProg B C) (h : ForwardProg Q) :
    ForwardProg (closeProg E F Q) :=
  ⟨⟨rfl, trivial⟩, forwardProg_bindVars _ _ _ h,
    forwardProg_of_loopFree (loopFree_constProg _)⟩

lemma forwardProg_resim (L : List (Bool × ℕ)) (hL : ∀ q ∈ L, q.1 = true) (p : ForProg A B)
    (hp : p.LoopFree) (Y : List ℕ) (fl fl' : ℕ) (q : B → Bool) :
    ForwardProg (resim L p Y fl fl' q : ForProg A C) :=
  ⟨forwardProg_of_loopFree (loopFree_clearBools _),
    forwardProg_nestLoops L _ hL
      ⟨forwardProg_of_loopFree (loopFree_markOut fl' _ hp), trivial⟩,
    forwardProg_of_loopFree (ForProg.loopFree_renamePos _ _ (loopFree_markOut fl q hp))⟩

lemma forwardProg_preTest (L : List (Bool × ℕ)) (hL : ∀ q ∈ L, q.1 = true) (p : ForProg A B)
    (hp : p.LoopFree) (base flQ flS : ℕ) (env : ℕ → ℕ) :
    ∀ t : ForTest B, ForwardProg (preTest L p base flQ flS env t : ForProg A C)
  | ForTest.label _ _ => forwardProg_resim L hL p hp _ _ _ _
  | ForTest.boolVar _ => trivial
  | ForTest.eqPos _ _ => trivial
  | ForTest.lePos _ _ => trivial
  | ForTest.not _ => trivial
  | ForTest.and _ _ => trivial
  | ForTest.or _ _ => trivial

lemma fst_mem_loopNest_true (L : List (Bool × ℕ)) (base lvl : ℕ) (hL : ∀ q ∈ L, q.1 = true) :
    ∀ q ∈ loopNest L base lvl true, q.1 = true := by
  intro q hq
  have hq' : q ∈ (L.map Prod.fst).zip (blk L base lvl) := by
    simpa [loopNest] using hq
  have := List.of_mem_zip hq'
  obtain ⟨x, hx, hxq⟩ := List.mem_map.mp this.1
  rw [← hxq]
  exact hL x hx

/-- **The translation of the outer for-transducer keeps the direction of every loop.**  The loops
of `Transducers.tr` are those of the nest of the inner transducer, so the translation of a forward
program by a forward nest is forward. -/
lemma forwardProg_tr (L : List (Bool × ℕ)) (hL : ∀ q ∈ L, q.1 = true) (p : ForProg A B)
    (hp : p.LoopFree) (base flQ flS : ℕ) :
    ∀ (Q : ForProg B C) (env : ℕ → ℕ) (lvl : ℕ), ForwardProg Q →
      ForwardProg (tr L p base flQ flS env lvl Q) := by
  intro Q
  induction Q with
  | skip => intro _ _ _; trivial
  | output c => intro _ _ _; trivial
  | assign i v => intro _ _ _; trivial
  | seq S T ihS ihT => intro env lvl h; exact ⟨ihS env lvl h.1, ihT env lvl h.2⟩
  | ite t S T ihS ihT =>
      intro env lvl h
      exact ⟨forwardProg_preTest L hL p hp base flQ flS env t, ihS env lvl h.1, ihT env lvl h.2⟩
  | loop d y S ih =>
      intro env lvl h
      have hd : d = true := h.1
      subst hd
      refine forwardProg_nestLoops _ _ (fst_mem_loopNest_true L base lvl hL) ?_
      exact ⟨forwardProg_resim L hL p hp _ _ _ _,
        ih (Function.update env y lvl) (lvl + 1) h.2, trivial⟩

/-- **The composed program is forward.** -/
lemma forwardProg_compProgAt (P : ForProg A B) (Q : ForProg B C) (L : List (Bool × ℕ))
    (p : ForProg A B) (base flQ flS X Y N : ℕ) (hL : ∀ q ∈ L, q.1 = true) (hp : p.LoopFree)
    (hQ : ForwardProg Q) : ForwardProg (compProgAt P Q L p base flQ flS X Y N) :=
  ⟨forwardProg_lenProg X Y,
    forwardProg_tr L hL p hp base flQ flS _ _ _
      (forwardProg_closeProg N (N + 1) _ (forwardProg_atomize Q hQ)),
    forwardProg_of_loopFree
      (loopFree_cpsFree _ (loopFree_shortSim X P) _ (fun _ => loopFree_constProg _))⟩

/-! ## The forward nest form -/

/-- **Every forward for-program is computed by a nest of first-to-last loops, on the inputs of
length at least two.**  This is `Transducers.for_nest_form` with the direction of every loop
tracked: the nest is the one of the forward prenex form. -/
theorem for_nest_form_fwd (P : ForProg A B) (hP : ForwardProg P) :
    ∃ (L : List (Bool × ℕ)) (p : ForProg A B), (∀ q ∈ L, q.1 = true) ∧ p.LoopFree ∧
      p.OutputsAtMostOne ∧ (L.map Prod.snd).Nodup ∧
      ∀ w : List A, 2 ≤ w.length →
        (ForProg.exec w (ForProg.nestLoops L p) (fun _ => 0) (fun _ => false)).2 = P.eval w := by
  classical
  set m : ℕ := maxList (P.posVars ++ P.boolVars) with hm
  obtain ⟨L, b, k', htr⟩ : ∃ L b k', trFor (m + 1) (m + 2) P (m + 3) = (L, b, k') :=
    ⟨_, _, _, rfl⟩
  have hPpos : ∀ i ∈ P.posVars, i < m + 1 := fun i hi => by
    have := le_maxList (P.posVars ++ P.boolVars) i (by simp [hi]); omega
  have hPbool : ∀ i ∈ P.boolVars, i < m + 1 := fun i hi => by
    have := le_maxList (P.posVars ++ P.boolVars) i (by simp [hi]); omega
  have ok := trFor_ok (m + 1) (m + 2) P (m + 3) L b k' htr
  have hLfwd : ∀ q ∈ L, q.1 = true := fwd_trFor (m + 1) (m + 2) P (m + 3) L b k' hP htr
  refine ⟨(true, m + 1) :: (true, m + 2) :: (true, k') :: L,
    prenexBodyF (m + 1) (m + 2) k' (k' + 1) (k' + 2) (k' + 3) b, ?_,
    loopFree_prenexBodyF _ _ _ _ _ _ b ok.loopFree,
    outputsAtMostOne_prenexBodyF _ _ _ _ _ _ b ok.out1, ?_, ?_⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · exact hLfwd q hq
  · have hmono := ok.mono
    have hrange := ok.loopRange
    simp only [List.map_cons, List.nodup_cons, List.mem_cons]
    refine ⟨?_, ?_, ?_, ok.nodup⟩
    · rintro (h | h | h)
      · omega
      · omega
      · have := hrange _ h; omega
    · rintro (h | h)
      · omega
      · have := hrange _ h; omega
    · intro h
      have := hrange _ h; omega
  · intro w hbig
    obtain ⟨s, -, h⟩ := exec_nest_big_fwd P (m + 1) (m + 2) (m + 3) L b k' (by omega) (by omega)
      (by omega) hPpos hPbool htr w hbig
    rw [h]
    rfl

/-! ## The forward prenex normal form -/

/-- **Lemma `lemma:prenex-normal-form` for forward programs.**  Every forward for-program is
equivalent to a forward program in prenex form. -/
theorem forwardPrenex (P : ForProg A B) (hP : ForwardProg P) :
    ∃ (ls : List (Bool × ℕ)) (body epilogue : ForProg A B),
      (∀ q ∈ ls, q.1 = true) ∧ body.LoopFree ∧ epilogue.LoopFree ∧
        ForProg.OutputsAtMostOne body ∧
        ∀ w, (ForProg.seq (ForProg.nestLoops ls body) epilogue).eval w = P.eval w := by
  classical
  set m : ℕ := maxList (P.posVars ++ P.boolVars) with hm
  obtain ⟨L, b, k', htr⟩ : ∃ L b k', trFor (m + 1) (m + 2) P (m + 3) = (L, b, k') :=
    ⟨_, _, _, rfl⟩
  have hPpos : ∀ i ∈ P.posVars, i < m + 1 := fun i hi => by
    have := le_maxList (P.posVars ++ P.boolVars) i (by simp [hi]); omega
  have hPbool : ∀ i ∈ P.boolVars, i < m + 1 := fun i hi => by
    have := le_maxList (P.posVars ++ P.boolVars) i (by simp [hi]); omega
  have ok := trFor_ok (m + 1) (m + 2) P (m + 3) L b k' htr
  have hk : m + 3 ≤ k' := ok.mono
  have hPpos' : ∀ i ∈ P.posVars, i < m + 3 := fun i hi => by have := hPpos i hi; omega
  have hPbool' : ∀ i ∈ P.boolVars, i < m + 3 := fun i hi => by have := hPbool i hi; omega
  have hGP : (k' + 2) ∉ P.boolVars := fun h => by have := hPbool' _ h; omega
  have hLfwd : ∀ q ∈ L, q.1 = true := fwd_trFor (m + 1) (m + 2) P (m + 3) L b k' hP htr
  refine ⟨(true, m + 1) :: (true, m + 2) :: (true, k') :: L,
    prenexBodyF (m + 1) (m + 2) k' (k' + 1) (k' + 2) (k' + 3) b,
    ForProg.ite (ForTest.boolVar (k' + 3)) ForProg.skip (shortSim (k' + 2) P), ?_,
    loopFree_prenexBodyF _ _ _ _ _ _ b ok.loopFree, ⟨trivial, loopFree_shortSim _ P⟩,
    outputsAtMostOne_prenexBodyF _ _ _ _ _ _ b ok.out1, ?_⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · exact hLfwd q hq
  intro w
  rw [ForProg.eval, exec_seq]
  by_cases hbig : 2 ≤ w.length
  · obtain ⟨s, hsH, hzvloop⟩ :=
      exec_nest_big_fwd P (m + 1) (m + 2) (m + 3) L b k' (by omega) (by omega) (by omega)
        hPpos hPbool htr w hbig
    have hsH' : ForTest.Holds w (fun _ => 0) s (ForTest.boolVar (k' + 3)) := hsH
    rw [hzvloop, exec_ite_pos _ _ _ _ _ _ hsH']
    simp [ForProg.exec, ForProg.eval]
  · -- the input has at most one letter: the nest does nothing but raise `G`
    have hshort : w.length ≤ 1 := by omega
    have hnest : ForProg.exec w (ForProg.nestLoops ((true, m + 1) :: (true, m + 2) :: (true, k')
          :: L) (prenexBodyF (m + 1) (m + 2) k' (k' + 1) (k' + 2) (k' + 3) b))
          (fun _ => 0) (fun _ => false)
        = (if 0 < w.length then Function.update (fun _ : ℕ => false) (k' + 2) true
            else (fun _ : ℕ => false), []) := by
      rcases Nat.lt_or_ge 0 w.length with h1 | h0
      · have hlen : w.length = 1 := by omega
        rw [if_pos h1, exec_nestLoops, hlen, tuplesOf_one, runList_one]
        rw [setTuple_zero _ _ (fun _ => rfl)]
        rw [prenexBodyF, exec_ite_neg _ _ _ _ _ _ (by simp [ForTest.Holds]),
          exec_ite_pos _ _ _ _ _ _ (by
            show (fun _ : ℕ => 0) (m + 1) = (fun _ : ℕ => 0) (m + 2)
            rfl)]
        rfl
      · have hlen : w.length = 0 := by omega
        rw [if_neg (by omega), exec_nest_cons,
          show loopRange true w.length = [] by simp [loopRange, hlen]]
        rfl
    rw [hnest]
    rcases Nat.lt_or_ge 0 w.length with h1 | h0
    · rw [if_pos h1]
      have hH : ¬ ForTest.Holds w (fun _ => 0)
          (Function.update (fun _ : ℕ => false) (k' + 2) true) (ForTest.boolVar (k' + 3)) := by
        show ¬ (_ = true)
        rw [Function.update_of_ne (by omega)]
        simp
      rw [exec_ite_neg _ _ _ _ _ _ hH,
        shortSim_spec (k' + 2) w hshort _ (fun _ => rfl) P hGP _ (by
          rw [Function.update_self]; simp [h1])]
      have hbv := exec_congr_bv w P (fun _ => 0) (fun i => i ∈ P.boolVars) (fun i hi => hi)
        (Function.update (fun _ : ℕ => false) (k' + 2) true) (fun _ => false) ?_
      · rw [hbv.1]
        simp [ForProg.eval]
      · intro i hi
        have := hPbool' i hi
        rw [Function.update_of_ne (by omega)]
    · rw [if_neg (by omega)]
      rw [exec_ite_neg _ _ _ _ _ _ (by show ¬ (_ = true); simp)]
      rw [shortSim_spec (k' + 2) w hshort _ (fun _ => rfl) P hGP _ (by
        have hlen : w.length = 0 := by omega
        simp [hlen])]
      simp [ForProg.eval]

/-! ## Closure under composition -/

/-- **Forward for-transducers are closed under composition.**  This is Lemma
`lem:for-closed-under-composition` with the direction of every loop tracked. -/
theorem isForwardFor_comp {f : List A → List B} {g : List B → List C}
    (hf : IsForwardFor f) (hg : IsForwardFor g) : IsForwardFor (g ∘ f) := by
  classical
  obtain ⟨P, hPf, hP⟩ := hf
  obtain ⟨Q, hQf, hQ⟩ := hg
  obtain ⟨L, p, hLfwd, hpLF, hpout, hpnd, hnest⟩ := for_nest_form_fwd P hPf
  set M : ℕ :=
    maxList (p.posVars ++ p.boolVars ++ L.map Prod.snd ++ P.posVars ++ P.boolVars) with hM
  set N : ℕ := maxList (ForProg.atomize Q).boolVars + 1 with hN
  refine ⟨compProgAt P Q L p (M + 3) (M + 1) (M + 2) (M + 3) (M + 5) N,
    forwardProg_compProgAt P Q L p _ _ _ _ _ _ hLfwd hpLF hQf, fun w => ?_⟩
  rw [eval_compProgAt P Q L p M N (M + 3) (M + 1) (M + 2) (M + 3) (M + 5) rfl rfl rfl rfl rfl
    (fun x hx => le_maxList _ x hx)
    (fun i hi => by have := le_maxList (ForProg.atomize Q).boolVars i hi; omega)
    hpLF hpout hpnd hnest w, hP w]
  exact hQ (f w)

end Exercises
end Transducers
