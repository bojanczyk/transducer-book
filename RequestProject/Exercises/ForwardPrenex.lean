/-
Exercise `exer:forward-for-transducer` of the chapter *For-transducers*
(`polyregular-for.tex`) of *Transducers* (M. Bojańczyk) -- the **forward prenex normal form**.

Lemma `lemma:prenex-normal-form` is proved in `RequestProject/PartD/ForPrenexTop.lean` by putting
the translation `Transducers.trFor` of the program under three extra loops,

  `for zv in positions: for lv in positions_reverse: for g in positions: …`

the second of which is of the *last-to-first* kind.  Its only purpose is to bind `lv` to the last
position of the input: the translation needs two designated positions, one to run the first half
of a sequential composition at and one to run the second half at, and it needs to know when the
innermost of the three extra loops is over so that it can set the flag that stops the work.

That last-to-first loop is the *only* one that the construction of the book introduces: the
translation `Transducers.trFor` reproduces the direction of every loop of the program it is given
(`Transducers.Exercises.fwd_trFor` below), and the extra loop that it adds for a sequential
composition, in `Transducers.mergeLoops`, is first-to-last.  So the construction as written does
turn a forward program into a program with one last-to-first loop, and something has to be
changed.

The change made here is that the two designated positions are the **first and the second**
position of the input, rather than the first and the last.  Nothing in the merging construction
uses that the second designated position is the last one -- only that it comes after the first --
so `Transducers.exec_merge` and `Transducers.trFor_spec` have been generalised, in place, to two
designated positions in increasing order, and both prenex forms are instances of them.  The second
position is bound by a *first-to-last* loop, whose second iteration it is; the pass at the first
iteration, where the two designated variables are equal, does nothing but raise the flag saying
that the input is nonempty, and the pass at the second iteration does the work at its first
iteration of the innermost extra loop and stops at its second one.  This is why the innermost
extra loop is still needed, and why the input is assumed to have at least two letters, exactly as
in the book.
-/
import RequestProject.Exercises.ForwardFor
import RequestProject.PartD.ForPrenexTop

namespace Transducers
namespace Exercises

open scoped Classical

variable {A B : Type}

/-! ## The loops of the translation are those of the program -/

/-- **The translation `Transducers.trFor` never introduces a last-to-first loop.**  It reproduces
the direction of every loop of the program it translates, and the extra loop it adds for a
sequential composition or a conditional is of the first-to-last kind. -/
lemma fwd_trFor (zv lv : ℕ) : ∀ (P : ForProg A B) (k : ℕ) (L : List (Bool × ℕ))
    (b : ForProg A B) (k' : ℕ), ForwardProg P → trFor zv lv P k = (L, b, k') →
    ∀ q ∈ L, q.1 = true := by
  intro P
  induction P with
  | skip => rintro k L b k' - heq; simp only [trFor, Prod.mk.injEq] at heq
            obtain ⟨rfl, -, -⟩ := heq; simp
  | output c => rintro k L b k' - heq; simp only [trFor, Prod.mk.injEq] at heq
                obtain ⟨rfl, -, -⟩ := heq; simp
  | assign i v => rintro k L b k' - heq; simp only [trFor, Prod.mk.injEq] at heq
                  obtain ⟨rfl, -, -⟩ := heq; simp
  | seq P Q ihP ihQ =>
      rintro k L b k' hfwd heq
      rcases hr₁ : trFor zv lv P (k + 1) with ⟨L₁, b₁, k₁⟩
      rcases hr₂ : trFor zv lv Q k₁ with ⟨L₂, b₂, k₂⟩
      simp only [trFor, hr₁, hr₂, Prod.mk.injEq] at heq
      obtain ⟨rfl, -, -⟩ := heq
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · rfl
      · rcases List.mem_append.mp hq' with h | h
        · exact ihP _ _ _ _ hfwd.1 hr₁ q h
        · exact ihQ _ _ _ _ hfwd.2 hr₂ q h
  | ite t P Q ihP ihQ =>
      rintro k L b k' hfwd heq
      rcases hr₁ : trFor zv lv P (k + 3) with ⟨L₁, b₁, k₁⟩
      rcases hr₂ : trFor zv lv Q k₁ with ⟨L₂, b₂, k₂⟩
      simp only [trFor, hr₁, hr₂, Prod.mk.injEq] at heq
      obtain ⟨rfl, -, -⟩ := heq
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · rfl
      · rcases List.mem_append.mp hq' with h | h
        · rcases List.mem_cons.mp h with rfl | h'
          · rfl
          · rcases List.mem_append.mp h' with h'' | h''
            · simp at h''
            · exact ihP _ _ _ _ hfwd.1 hr₁ q h''
        · exact ihQ _ _ _ _ hfwd.2 hr₂ q h
  | loop d x P ih =>
      rintro k L b k' hfwd heq
      rcases hr : trFor zv lv P (k + 1) with ⟨L₁, b₁, k₁⟩
      simp only [trFor, hr, Prod.mk.injEq] at heq
      obtain ⟨rfl, -, -⟩ := heq
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact hfwd.1
      · exact ih _ _ _ _ hfwd.2 hr q hq'

/-! ## The body of the forward nest -/

/-- The body of the single nest of loops of the forward prenex form.  The variable `g` is the
innermost of the three extra loops, `dn` is the flag saying that the work is over, and `G` and `H`
tell the epilogue whether the input has at least one, respectively at least two letters.

While `dn` is false, the pass where the two designated variables `zv` and `sv` are equal -- the
first pass of the loop on `sv`, and the only one if the input has one letter -- raises `G`, and the
next pass, where `sv` is the second position, runs the translated body `b` at the iterations with
`g = zv` and, at the next iteration of the loop on `g`, raises `H` and sets `dn`. -/
def prenexBodyF (zv sv g dn G H : ℕ) (b : ForProg A B) : ForProg A B :=
  ForProg.ite (ForTest.boolVar dn) ForProg.skip
    (ForProg.ite (ForTest.eqPos zv sv) (ForProg.assign G true)
      (ForProg.ite (ForTest.eqPos g zv) b
        (ForProg.seq (ForProg.assign H true) (ForProg.assign dn true))))

lemma loopFree_prenexBodyF (zv sv g dn G H : ℕ) (b : ForProg A B) (hb : b.LoopFree) :
    (prenexBodyF zv sv g dn G H b).LoopFree :=
  ⟨trivial, trivial, hb, trivial, trivial⟩

lemma outputsAtMostOne_prenexBodyF (zv sv g dn G H : ℕ) (b : ForProg A B)
    (hb : b.OutputsAtMostOne) : (prenexBodyF zv sv g dn G H b).OutputsAtMostOne := by
  intro w pos bv
  simp only [prenexBodyF, ForProg.exec]
  split
  · simp
  · split
    · simp
    · split
      · exact hb w pos bv
      · simp

/-- Once the flag `dn` is up, the body does nothing. -/
lemma exec_prenexBodyF_dead (w : List A) (zv sv g dn G H : ℕ) (b : ForProg A B) (pos : ℕ → ℕ)
    (s : ℕ → Bool) (hs : s dn = true) :
    ForProg.exec w (prenexBodyF zv sv g dn G H b) pos s = (s, []) := by
  simp [prenexBodyF, ForProg.exec, ForTest.Holds, hs]

/-- Once the flag `dn` is up, a whole nest of loops over the body does nothing. -/
lemma exec_nest_prenexBodyF_dead (w : List A) (zv sv g dn G H : ℕ) (b : ForProg A B)
    (L : List (Bool × ℕ)) (pos : ℕ → ℕ) (s : ℕ → Bool) (hs : s dn = true) :
    ForProg.exec w (ForProg.nestLoops L (prenexBodyF zv sv g dn G H b)) pos s = (s, []) :=
  nest_noop w L _ pos s (fun _ => exec_prenexBodyF_dead w zv sv g dn G H b _ s hs)

/-! ## The first two iterations of a first-to-last loop -/

lemma range_eq_zero_one_cons {n : ℕ} (hn : 2 ≤ n) : ∃ l, List.range n = 0 :: 1 :: l := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine ⟨((List.range m).map Nat.succ).map Nat.succ, ?_⟩
  rw [List.range_succ_eq_map, List.range_succ_eq_map]
  simp

/-! ## The nest of loops of the forward prenex form -/

/-- **The forward nest of loops computes the program, on inputs of length at least two.** -/
theorem exec_nest_big_fwd (P : ForProg A B) (zv sv k₀ : ℕ) (L : List (Bool × ℕ))
    (b : ForProg A B) (k' : ℕ) (hzv : zv < k₀) (hzl : zv < sv) (hsv : sv < k₀)
    (hPpos : ∀ i ∈ P.posVars, i < zv) (hPbool : ∀ i ∈ P.boolVars, i < zv)
    (htr : trFor zv sv P k₀ = (L, b, k')) (w : List A) (hbig : 2 ≤ w.length) :
    ∃ s : ℕ → Bool, s (k' + 3) = true ∧
      ForProg.exec w (ForProg.nestLoops ((true, zv) :: (true, sv) :: (true, k') :: L)
          (prenexBodyF zv sv k' (k' + 1) (k' + 2) (k' + 3) b)) (fun _ => 0) (fun _ => false)
        = (s, (ForProg.exec w P (fun _ => 0) (fun _ => false)).2) := by
  classical
  have ok : TrOk zv sv P k₀ L b k' := trFor_ok zv sv P k₀ L b k' htr
  have hk : k₀ ≤ k' := ok.mono
  have hzP : zv ∉ P.posVars := fun h => by have := hPpos zv h; omega
  have hsP : sv ∉ P.posVars := fun h => by have := hPpos sv h; omega
  have hPpos' : ∀ i ∈ P.posVars, i < k₀ := fun i hi => by have := hPpos i hi; omega
  have hPbool' : ∀ i ∈ P.boolVars, i < k₀ := fun i hi => by have := hPbool i hi; omega
  have hbbool : ∀ i ∈ b.boolVars, i < k' := by
    intro i hi
    rcases ok.boolOk i hi with h | h
    · have := hPbool' i h; omega
    · omega
  have hbdn : (k' + 1) ∉ b.boolVars := fun h => by have := hbbool _ h; omega
  have hbH : (k' + 3) ∉ b.boolVars := fun h => by have := hbbool _ h; omega
  have hnotL : ∀ i : ℕ, (i < k₀ ∨ k' ≤ i) → i ∉ L.map Prod.snd := by
    intro i hi hmem
    have := ok.loopRange i hmem
    omega
  set body : ForProg A B := prenexBodyF zv sv k' (k' + 1) (k' + 2) (k' + 3) b with hbodydef
  have hn0 : 0 < w.length := by omega
  -- the position valuation inside the two passes of the loop on `sv`
  set pp : ℕ → ℕ → ℕ → ℕ :=
    fun q gg => Function.update (Function.update (fun _ : ℕ => 0) sv q) k' gg with hppdef
  have hppz : ∀ q gg, pp q gg zv = 0 := by
    intro q gg
    rw [hppdef]
    show Function.update (Function.update (fun _ : ℕ => 0) sv q) k' gg zv = 0
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hpps : ∀ q gg, pp q gg sv = q := by
    intro q gg
    rw [hppdef]
    show Function.update (Function.update (fun _ : ℕ => 0) sv q) k' gg sv = q
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hppg : ∀ q gg, pp q gg k' = gg := by
    intro q gg
    rw [hppdef]
    exact Function.update_self _ _ _
  have hset : ∀ (t : List ℕ) (q gg i : ℕ), (i < k₀ ∨ k' ≤ i) →
      setTuple L t (pp q gg) i = pp q gg i :=
    fun t q gg i hi => setTuple_of_not_mem L t _ (hnotL i hi)
  have hsz : ∀ (t : List ℕ) (q gg : ℕ), setTuple L t (pp q gg) zv = 0 := by
    intro t q gg; rw [hset t q gg zv (Or.inl hzv), hppz]
  have hss : ∀ (t : List ℕ) (q gg : ℕ), setTuple L t (pp q gg) sv = q := by
    intro t q gg; rw [hset t q gg sv (Or.inl hsv), hpps]
  have hsg : ∀ (t : List ℕ) (q gg : ℕ), setTuple L t (pp q gg) k' = gg := by
    intro t q gg; rw [hset t q gg k' (Or.inr le_rfl), hppg]
  -- ## the pass with `sv` at the first position: only the flag `G` is raised
  have hleafG : ∀ (t : List ℕ) (gg : ℕ) (s : ℕ → Bool), s (k' + 1) = false →
      ForProg.exec w body (setTuple L t (pp 0 gg)) s = (Function.update s (k' + 2) true, []) := by
    intro t gg s hs
    rw [hbodydef, prenexBodyF]
    rw [exec_ite_neg _ _ _ _ _ _ (by show ¬ (s (k' + 1) = true); rw [hs]; simp),
      exec_ite_pos _ _ _ _ _ _ (by
        show setTuple L t (pp 0 gg) zv = setTuple L t (pp 0 gg) sv
        rw [hsz t 0 gg, hss t 0 gg])]
    rfl
  have hleafGdead : ∀ (t : List ℕ) (gg : ℕ) (s : ℕ → Bool), s (k' + 2) = true →
      ForProg.exec w body (setTuple L t (pp 0 gg)) s = (s, []) := by
    intro t gg s hs
    by_cases hdn : s (k' + 1) = true
    · rw [hbodydef]; exact exec_prenexBodyF_dead w zv sv k' (k' + 1) (k' + 2) (k' + 3) b _ s hdn
    · rw [hleafG t gg s (by simpa using hdn), ← hs, Function.update_eq_self]
  have hAstep : ∀ (gg : ℕ) (s : ℕ → Bool), s (k' + 2) = true →
      ForProg.exec w (ForProg.nestLoops L body) (pp 0 gg) s = (s, []) := by
    intro gg s hs
    exact nest_noop w L body _ s (fun t => hleafGdead t gg s hs)
  have hAfirst : ∀ (gg : ℕ) (s : ℕ → Bool), s (k' + 1) = false →
      ForProg.exec w (ForProg.nestLoops L body) (pp 0 gg) s
        = (Function.update s (k' + 2) true, []) := by
    intro gg s hs
    rw [nest_kill w L body (pp 0 gg) s (fun s' => s' (k' + 2) = true) hn0
      (fun t s' hs' => hleafGdead t gg s' hs')
      (by rw [hleafG _ gg s hs]; simp)]
    exact hleafG _ gg s hs
  have hA : ForProg.exec w (ForProg.nestLoops ((true, k') :: L) body)
        (Function.update (fun _ : ℕ => 0) sv 0) (fun _ => false)
      = (Function.update (fun _ : ℕ => false) (k' + 2) true, []) := by
    obtain ⟨l, hl⟩ := loopRange_eq_cons (n := w.length) true hn0
    have hl' : loopRange true w.length = 0 :: l := by simpa using hl
    rw [exec_nest_cons, hl']
    have hpp0 : ∀ gg : ℕ,
        Function.update (Function.update (fun _ : ℕ => 0) sv 0) k' gg = pp 0 gg := fun _ => rfl
    rw [runList_head_dead _ _ _ _ ?_]
    · rw [hpp0 0, hAfirst 0 (fun _ => false) rfl]
    · intro t _
      rw [hpp0 0, hAfirst 0 (fun _ => false) rfl, hpp0 t]
      exact hAstep t _ (by simp)
  -- ## the pass with `sv` at the second position: the work is done
  have hguard : ∀ (t : List ℕ) (s : ℕ → Bool), s (k' + 1) = false →
      ForProg.exec w body (setTuple L t (pp 1 0)) s
        = ForProg.exec w b (setTuple L t (pp 1 0)) s := by
    intro t s hs
    rw [hbodydef, prenexBodyF]
    rw [exec_ite_neg _ _ _ _ _ _ (by show ¬ (s (k' + 1) = true); rw [hs]; simp),
      exec_ite_neg _ _ _ _ _ _ (by
        show ¬ (setTuple L t (pp 1 0) zv = setTuple L t (pp 1 0) sv)
        rw [hsz t 1 0, hss t 1 0]; omega),
      exec_ite_pos _ _ _ _ _ _ (by
        show setTuple L t (pp 1 0) k' = setTuple L t (pp 1 0) zv
        rw [hsg t 1 0, hsz t 1 0])]
  have hcongr : ForProg.exec w (ForProg.nestLoops L body) (pp 1 0) (Function.update
        (fun _ : ℕ => false) (k' + 2) true)
      = ForProg.exec w (ForProg.nestLoops L b) (pp 1 0)
        (Function.update (fun _ : ℕ => false) (k' + 2) true) := by
    refine nest_congr w L body b _ _ (fun s => s (k' + 1) = false) (by simp) hguard ?_
    intro t s hs
    rw [hguard t s hs, ForProg.exec_bv_unchanged w b _ s hbdn]
    exact hs
  have hspec := trFor_spec zv sv k₀ hzv hsv w P hPpos' hPbool' hzP hsP k₀ L b k' htr le_rfl
    (pp 1 0) (by rw [hppz, hpps]; omega) (by rw [hpps]; omega)
    (Function.update (fun _ : ℕ => false) (k' + 2) true) (fun _ => false)
    (fun i hi => by rw [Function.update_of_ne (by omega)])
  have hposP : ForProg.exec w P (pp 1 0) (fun _ => false)
      = ForProg.exec w P (fun _ => 0) (fun _ => false) := by
    refine ForProg.exec_congr_pos w P _ _ _ (fun i hi => ?_)
    have h2 : i < zv := hPpos i hi
    rw [hppdef]
    show Function.update (Function.update (fun _ : ℕ => 0) sv 1) k' 0 i = 0
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  set s₄ : ℕ → Bool := (ForProg.exec w (ForProg.nestLoops L b) (pp 1 0)
    (Function.update (fun _ : ℕ => false) (k' + 2) true)).1 with hs4def
  have hstep0 : ForProg.exec w (ForProg.nestLoops L body) (pp 1 0)
        (Function.update (fun _ : ℕ => false) (k' + 2) true)
      = (s₄, (ForProg.exec w P (fun _ => 0) (fun _ => false)).2) := by
    rw [hcongr]
    refine Prod.ext rfl ?_
    rw [hs4def, hspec.1, hposP]
  have hs4dn : s₄ (k' + 1) = false := by
    rw [hs4def]
    have := nest_bv_fix w L b (pp 1 0) (Function.update (fun _ : ℕ => false) (k' + 2) true)
      (k' + 1) (fun t s => ForProg.exec_bv_unchanged w b _ s hbdn)
    rw [this, Function.update_of_ne (by omega)]
  have hs4H : s₄ (k' + 3) = false := by
    rw [hs4def]
    have := nest_bv_fix w L b (pp 1 0) (Function.update (fun _ : ℕ => false) (k' + 2) true)
      (k' + 3) (fun t s => ForProg.exec_bv_unchanged w b _ s hbH)
    rw [this, Function.update_of_ne (by omega)]
  have hkill : ∀ (t : List ℕ) (s : ℕ → Bool), s (k' + 1) = false →
      ForProg.exec w body (setTuple L t (pp 1 1)) s
        = (Function.update (Function.update s (k' + 3) true) (k' + 1) true, []) := by
    intro t s hs
    rw [hbodydef, prenexBodyF]
    rw [exec_ite_neg _ _ _ _ _ _ (by show ¬ (s (k' + 1) = true); rw [hs]; simp),
      exec_ite_neg _ _ _ _ _ _ (by
        show ¬ (setTuple L t (pp 1 1) zv = setTuple L t (pp 1 1) sv)
        rw [hsz t 1 1, hss t 1 1]; omega),
      exec_ite_neg _ _ _ _ _ _ (by
        show ¬ (setTuple L t (pp 1 1) k' = setTuple L t (pp 1 1) zv)
        rw [hsg t 1 1, hsz t 1 1]; omega)]
    show ((ForProg.exec w (ForProg.assign (k' + 1) true) _
      (Function.update s (k' + 3) true)).1, _) = _
    simp [ForProg.exec]
  have hstep1 : ForProg.exec w (ForProg.nestLoops L body) (pp 1 1) s₄
      = (Function.update (Function.update s₄ (k' + 3) true) (k' + 1) true, []) := by
    rw [nest_kill w L body (pp 1 1) s₄ (fun s => s (k' + 1) = true) hn0
      (fun t s hs => by
        rw [hbodydef]
        exact exec_prenexBodyF_dead w zv sv k' (k' + 1) (k' + 2) (k' + 3) b _ s hs)
      (by rw [hkill _ s₄ hs4dn]; simp)]
    exact hkill _ s₄ hs4dn
  have hB : ForProg.exec w (ForProg.nestLoops ((true, k') :: L) body)
        (Function.update (fun _ : ℕ => 0) sv 1)
        (Function.update (fun _ : ℕ => false) (k' + 2) true)
      = (Function.update (Function.update s₄ (k' + 3) true) (k' + 1) true,
        (ForProg.exec w P (fun _ => 0) (fun _ => false)).2) := by
    obtain ⟨l, hl⟩ := range_eq_zero_one_cons (n := w.length) hbig
    have hl' : loopRange true w.length = 0 :: 1 :: l := by
      show List.range w.length = _
      exact hl
    have hppq : ∀ gg : ℕ,
        Function.update (Function.update (fun _ : ℕ => 0) sv 1) k' gg = pp 1 gg := fun _ => rfl
    rw [exec_nest_cons, hl', runList_cons, hppq 0, hstep0, runList_cons, hppq 1, hstep1]
    rw [runList_noop _ l _ (fun t _ => by
      rw [hppq t]
      exact exec_nest_prenexBodyF_dead w zv sv k' (k' + 1) (k' + 2) (k' + 3) b _ _ _ (by simp))]
    simp
  -- ## the loop on `sv`
  have hsvloop : ForProg.exec w (ForProg.nestLoops ((true, sv) :: (true, k') :: L) body)
        (fun _ => 0) (fun _ => false)
      = (Function.update (Function.update s₄ (k' + 3) true) (k' + 1) true,
        (ForProg.exec w P (fun _ => 0) (fun _ => false)).2) := by
    obtain ⟨l, hl⟩ := range_eq_zero_one_cons (n := w.length) hbig
    have hl' : loopRange true w.length = 0 :: 1 :: l := by
      show List.range w.length = _
      exact hl
    rw [exec_nest_cons, hl', runList_cons, hA, runList_cons, hB]
    rw [runList_noop _ l _ (fun t _ =>
      exec_nest_prenexBodyF_dead w zv sv k' (k' + 1) (k' + 2) (k' + 3) b _ _ _ (by simp))]
    simp
  -- ## the loop on `zv`
  have hzvloop : ForProg.exec w (ForProg.nestLoops ((true, zv) :: (true, sv) :: (true, k') :: L)
        body) (fun _ => 0) (fun _ => false)
      = (Function.update (Function.update s₄ (k' + 3) true) (k' + 1) true,
        (ForProg.exec w P (fun _ => 0) (fun _ => false)).2) := by
    obtain ⟨l, hl⟩ := loopRange_eq_cons (n := w.length) true hn0
    have hl' : loopRange true w.length = 0 :: l := by simpa using hl
    have hupd0 : Function.update (fun _ : ℕ => 0) zv 0 = (fun _ : ℕ => 0) := by
      funext y
      by_cases hy : y = zv
      · subst hy; simp
      · simp [Function.update_of_ne hy]
    rw [exec_nest_cons, hl', runList_head_dead _ _ _ _ ?_]
    · simp only [hupd0]
      exact hsvloop
    · intro t _
      simp only [hupd0, hsvloop]
      exact exec_nest_prenexBodyF_dead w zv sv k' (k' + 1) (k' + 2) (k' + 3) b _ _ _ (by simp)
  exact ⟨_, by rw [Function.update_of_ne (by omega), Function.update_self], hzvloop⟩

end Exercises
end Transducers
