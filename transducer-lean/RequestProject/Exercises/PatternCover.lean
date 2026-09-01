/-
The structure of a regular language of polynomial growth: it is covered by finitely many
`k`-patterns.  This is the analysis of the strongly connected components of an automaton that the
author's solution to Exercise `exer:polynomial-ideals` of *Transducers* (M. Bojańczyk) asks for.
-/
import RequestProject.Exercises.ChainWords

/-!
# A regular language of growth `O(n^k)` is covered by finitely many `k`-patterns

`RequestProject/Exercises/RegularGrowth.lean` shows that a deterministic automaton with no
ambiguous cycle and no chain of `k+1` loops accepts `O(n^k)` words, by an induction that follows
the *forced path* inside a strongly connected component: at a state that lies on a loop, all but
one letter leave the component, and the letters that stay are determined.  The very same induction
gives the structure of the language, and that is what this file proves:

* `Transducers.Exercises.RegGrowth.exists_pattern_cover` — under the same hypotheses, there are
  finitely many `k`-patterns `us 0 · (xs 0)^* · us 1 ⋯ us k`
  (`Transducers.Exercises.chainWord`) such that every accepted word is one of their words.

The auxiliary material is:

* `Transducers.Exercises.RegGrowth.constPat`, `prependPat`, `consLoopPat` — the three ways in
  which the induction builds a pattern, and the corresponding equalities between their words;
* `Transducers.Exercises.RegGrowth.exists_forced_period`,
  `Transducers.Exercises.RegGrowth.loopWord_period` — the forced path is eventually periodic, so
  the words it reads form a single one-loop pattern, one for each phase.
-/

namespace Transducers.Exercises

open Transducers

namespace RegGrowth

/-! ### Building patterns -/

section Patterns

variable {A : Type}

@[simp] lemma loopPow_nil (n : ℕ) : loopPow ([] : List A) n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [loopPow_succ, ih, List.nil_append]

/-- The pattern with no loops whose only word is `u`. -/
def constPat (u : List A) : (ℕ → List A) × (ℕ → List A) :=
  (fun i => if i = 0 then u else [], fun _ => [])

/-- The pattern `P` with the word `v` written in front of it. -/
def prependPat (v : List A) (P : (ℕ → List A) × (ℕ → List A)) :
    (ℕ → List A) × (ℕ → List A) :=
  (fun i => if i = 0 then v ++ P.1 0 else P.1 i, P.2)

/-- The pattern `u · x^* · P`: one more loop in front of the pattern `P`. -/
def consLoopPat (u x : List A) (P : (ℕ → List A) × (ℕ → List A)) :
    (ℕ → List A) × (ℕ → List A) :=
  (fun i => if i = 0 then u else P.1 (i - 1), fun i => if i = 0 then x else P.2 (i - 1))

lemma chainWord_nil_nil (k : ℕ) (c : ℕ → ℕ) :
    chainWord (fun _ => ([] : List A)) (fun _ => []) k c = [] := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih => rw [chainWord_succ]; simpa using ih (fun i => c (i + 1))

@[simp] lemma chainWord_constPat (u : List A) (k : ℕ) (c : ℕ → ℕ) :
    chainWord (constPat u).1 (constPat u).2 k c = u := by
  cases k with
  | zero => rfl
  | succ k =>
      rw [chainWord_succ]
      have h1 : (fun i => (constPat u).1 (i + 1)) = fun _ => ([] : List A) := by
        funext i; simp [constPat]
      have h2 : (fun i => (constPat u).2 (i + 1)) = fun _ => ([] : List A) := by
        funext i; simp [constPat]
      rw [h1, h2, chainWord_nil_nil]
      simp [constPat]

lemma chainWord_congr_counts (us xs : ℕ → List A) (k : ℕ) {c c' : ℕ → ℕ}
    (h : ∀ i, i < k → c i = c' i) : chainWord us xs k c = chainWord us xs k c' := by
  induction k generalizing us xs c c' with
  | zero => rfl
  | succ k ih =>
      rw [chainWord_succ, chainWord_succ, h 0 (Nat.succ_pos k),
        ih (fun i => us (i + 1)) (fun i => xs (i + 1)) (c := fun i => c (i + 1))
          (c' := fun i => c' (i + 1)) (fun i hi => h (i + 1) (by omega))]

@[simp] lemma chainWord_prependPat (v : List A) (P : (ℕ → List A) × (ℕ → List A)) (k : ℕ)
    (c : ℕ → ℕ) :
    chainWord (prependPat v P).1 (prependPat v P).2 k c = v ++ chainWord P.1 P.2 k c :=
  chainWord_prepend v P.1 P.2 k c

lemma chainWord_consLoopPat (u x : List A) (P : (ℕ → List A) × (ℕ → List A)) (k : ℕ)
    (c : ℕ → ℕ) :
    chainWord (consLoopPat u x P).1 (consLoopPat u x P).2 (k + 1) c
      = u ++ loopPow x (c 0) ++ chainWord P.1 P.2 k (fun i => c (i + 1)) := by
  rw [chainWord_succ]
  have h1 : (fun i => (consLoopPat u x P).1 (i + 1)) = P.1 := by
    funext i; simp [consLoopPat]
  have h2 : (fun i => (consLoopPat u x P).2 (i + 1)) = P.2 := by
    funext i; simp [consLoopPat]
  rw [h1, h2]
  rfl

end Patterns

/-! ### The forced path is eventually periodic -/

section Period

variable {A σ : Type} (M : DFA A σ) (nxt : σ → A) (q : σ)

lemma loopState_add (t s : ℕ) :
    loopState M nxt q (t + s) = loopState M nxt (loopState M nxt q t) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      show M.step (loopState M nxt q (t + s)) (nxt (loopState M nxt q (t + s))) = _
      rw [ih]
      rfl

variable {M nxt q}

lemma exists_forced_period [Finite σ] :
    ∃ a d : ℕ, 0 < d ∧ loopState M nxt q (a + d) = loopState M nxt q a := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (loopState M nxt q)
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact ⟨i, j - i, by omega, by rw [show i + (j - i) = j by omega]; exact h.symm⟩
  · have hlt : j < i := by omega
    exact ⟨j, i - j, by omega, by rw [show j + (i - j) = i by omega]; exact h⟩

variable {a d : ℕ}

lemma loopState_period (h : loopState M nxt q (a + d) = loopState M nxt q a) (m : ℕ) :
    loopState M nxt q (a + d * m) = loopState M nxt q a := by
  induction m with
  | zero => simp
  | succ m ih =>
      have harg : a + d * (m + 1) = (a + d * m) + d := by ring
      rw [harg, loopState_add, ih, ← loopState_add, h]

lemma loopWord_period (h : loopState M nxt q (a + d) = loopState M nxt q a) (m : ℕ) :
    loopWord M nxt q (a + d * m)
      = loopWord M nxt q a ++ loopPow (loopWord M nxt (loopState M nxt q a) d) m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have harg : a + d * (m + 1) = (a + d * m) + d := by ring
      rw [harg, loopWord_add, ih, loopState_period h m, List.append_assoc]
      congr 1
      rw [loopPow_add (loopWord M nxt (loopState M nxt q a) d) m 1]
      simp [loopPow]

end Period

/-! ### The cover -/

section Cover

variable {A σ : Type} [Fintype A] [Fintype σ] {M : DFA A σ}

/-- **A regular language of polynomial growth is covered by finitely many patterns.**  If the
automaton has no ambiguous cycle and no chain of `k+1` loops from `q`, then there are finitely
many `k`-patterns such that every word accepted from `q` is one of their words.

The induction is the one of `Transducers.Exercises.RegGrowth.accCount_le_of_not_chain`: at a state
that lies on a loop, the letters that stay in the strongly connected component are forced, so the
accepted words either follow the forced path — which is eventually periodic, and so contributes
one pattern with a single loop for each phase — or follow it, leave the component, and continue
with a word accepted from a state of a strictly smaller component, to which the induction
hypothesis applies with one loop fewer. -/
theorem exists_pattern_cover (hamb : ¬ AmbCycle M) :
    ∀ (N : ℕ) (q : σ) (k : ℕ), (reachFin M q).card ≤ N → Reaches M M.start q →
      ¬ Chain M q (k + 1) →
      ∃ F : List ((ℕ → List A) × (ℕ → List A)),
        ∀ w : List A, M.evalFrom q w ∈ M.accept →
          ∃ P ∈ F, ∃ c : ℕ → ℕ, w = chainWord P.1 P.2 k c := by
  classical
  intro N
  induction N with
  | zero =>
      intro q k hcard _ _
      have : 0 < (reachFin M q).card :=
        Finset.card_pos.mpr ⟨q, mem_reachFin.mpr (reaches_refl q)⟩
      omega
  | succ N ih =>
      intro q k hcard hreach hnot
      by_cases huse : Useful M q
      swap
      · exact ⟨[], fun w hw => absurd ⟨w, hw⟩ huse⟩
      by_cases hloop : Loopy M q
      swap
      · -- no loop at `q`: every successor lies in a strictly smaller component
        have hstep : ∀ a : A, ∃ F : List ((ℕ → List A) × (ℕ → List A)),
            ∀ w : List A, M.evalFrom (M.step q a) w ∈ M.accept →
              ∃ P ∈ F, ∃ c : ℕ → ℕ, w = chainWord P.1 P.2 k c := by
          intro a
          have hns : ¬ Reaches M (M.step q a) q := by
            rintro ⟨w, hw⟩
            exact hloop ⟨a :: w, by simp, hw⟩
          have hcr : (reachFin M (M.step q a)).card ≤ N := by
            have := reachFin_card_lt (reaches_step q a) hns
            omega
          refine ih _ k hcr (reaches_trans hreach (reaches_step q a)) ?_
          intro hc
          exact hnot (chain_of_reaches (reaches_step q a) hc)
        choose Fa hFa using hstep
        refine ⟨constPat [] :: (Finset.univ : Finset A).toList.flatMap
          (fun a => (Fa a).map (prependPat [a])), fun w hw => ?_⟩
        cases w with
        | nil =>
            exact ⟨constPat [], List.mem_cons_self, fun _ => 0,
              (chainWord_constPat ([] : List A) k _).symm⟩
        | cons a z =>
            obtain ⟨P, hP, c, hc⟩ := hFa a z hw
            refine ⟨prependPat [a] P, List.mem_cons_of_mem _ ?_, c, ?_⟩
            · exact List.mem_flatMap.mpr ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a),
                List.mem_map_of_mem hP⟩
            · rw [chainWord_prependPat, ← hc]
              rfl
      · -- `q` lies on a loop: the letters that stay in its component are forced
        have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with rfl | h
          · exact absurd (⟨q, reaches_refl q, hloop, Or.inl ⟨rfl, huse⟩⟩ : Chain M q 1) hnot
          · exact h
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hAne : Nonempty A := by
          obtain ⟨x, hxne, -⟩ := hloop
          cases x with
          | nil => exact absurd rfl hxne
          | cons a _ => exact ⟨a⟩
        have hex : ∀ p : σ, ∃ a : A,
            (Reaches M q p ∧ Reaches M p q) → Reaches M (M.step p a) p := by
          intro p
          by_cases hp : Reaches M q p ∧ Reaches M p q
          · obtain ⟨⟨v, hv⟩, ⟨u, hu⟩⟩ := hp
            obtain ⟨x, hxne, hx⟩ := hloop
            have hw : M.evalFrom p (u ++ x ++ v) = p := by
              rw [M.evalFrom_of_append, M.evalFrom_of_append, hu, hx, hv]
            have hwne : u ++ x ++ v ≠ [] := by
              intro h
              have := congrArg List.length h
              simp only [List.length_append, List.length_nil] at this
              have : 0 < x.length := List.length_pos_iff.mpr hxne
              omega
            match hcons : u ++ x ++ v, hwne with
            | a :: w', _ => exact ⟨a, fun _ => ⟨w', by rw [hcons] at hw; exact hw⟩⟩
          · exact ⟨Classical.arbitrary A, fun h => absurd h hp⟩
        choose nxt hnxt using hex
        have huniq : ∀ p : σ, Reaches M q p → Reaches M p q → ∀ b : A, b ≠ nxt p →
            ¬ Reaches M (M.step p b) p := by
          intro p h1 h2 b hb hcon
          obtain ⟨wa, hwa⟩ := hnxt p ⟨h1, h2⟩
          obtain ⟨wb, hwb⟩ := hcon
          refine hamb (ambCycle_of_two_loops (q := p) (reaches_trans hreach h1)
            (useful_of_reaches h2 huse) (x := nxt p :: wa) (y := b :: wb) hwa hwb
            (by simp) (by simp) ?_)
          simp only [List.head?_cons, ne_eq, Option.some.injEq]
          exact fun h => hb h.symm
        have hscc : ∀ t : ℕ,
            Reaches M q (loopState M nxt q t) ∧ Reaches M (loopState M nxt q t) q := by
          intro t
          induction t with
          | zero => exact ⟨reaches_refl q, reaches_refl q⟩
          | succ t iht =>
              obtain ⟨h1, h2⟩ := iht
              exact ⟨reaches_trans h1 (reaches_step _ _), reaches_trans (hnxt _ ⟨h1, h2⟩) h2⟩
        have hexit : ∀ (t : ℕ) (b : A), b ≠ nxt (loopState M nxt q t) →
            Reaches M q (M.step (loopState M nxt q t) b) ∧
              ¬ Reaches M (M.step (loopState M nxt q t) b) q := by
          intro t b hb
          obtain ⟨h1, h2⟩ := hscc t
          refine ⟨reaches_trans h1 (reaches_step _ _), fun hr => ?_⟩
          exact huniq _ h1 h2 b hb (reaches_trans hr h1)
        have hkey : ∀ r : σ, ∃ F : List ((ℕ → List A) × (ℕ → List A)),
            (Reaches M q r ∧ ¬ Reaches M r q) →
              ∀ w : List A, M.evalFrom r w ∈ M.accept →
                ∃ P ∈ F, ∃ c : ℕ → ℕ, w = chainWord P.1 P.2 k' c := by
          intro r
          by_cases hr : Reaches M q r ∧ ¬ Reaches M r q
          · obtain ⟨h1, h2⟩ := hr
            have hcr : (reachFin M r).card ≤ N := by
              have := reachFin_card_lt h1 h2
              omega
            have hnc : ¬ Chain M r (k' + 1) := by
              intro hc
              exact hnot ⟨q, reaches_refl q, hloop, Or.inr ⟨r, h1, h2, hc⟩⟩
            obtain ⟨F, hF⟩ := ih r k' hcr (reaches_trans hreach h1) hnc
            exact ⟨F, fun _ => hF⟩
          · exact ⟨[], fun h => absurd h hr⟩
        choose Ff hFf using hkey
        obtain ⟨a, d, hdpos, hper⟩ :=
          exists_forced_period (M := M) (nxt := nxt) (q := q)
        refine ⟨((List.range a).map (fun s => constPat (loopWord M nxt q s))
            ++ (List.range d).map (fun j =>
              consLoopPat (loopWord M nxt q a) (loopWord M nxt (loopState M nxt q a) d)
                (constPat (loopWord M nxt (loopState M nxt q a) j))))
            ++ (List.range a).flatMap (fun s =>
              (Finset.univ : Finset A).toList.flatMap (fun b =>
                (Finset.univ : Finset σ).toList.flatMap (fun r =>
                  (Ff r).map (fun P => consLoopPat (loopWord M nxt q s ++ [b]) [] P))))
            ++ (List.range d).flatMap (fun j =>
              (Finset.univ : Finset A).toList.flatMap (fun b =>
                (Finset.univ : Finset σ).toList.flatMap (fun r =>
                  (Ff r).map (fun P => consLoopPat (loopWord M nxt q a)
                    (loopWord M nxt (loopState M nxt q a) d)
                    (prependPat (loopWord M nxt (loopState M nxt q a) j ++ [b]) P))))),
          fun w hw => ?_⟩
        have hstate0 : loopState M nxt q 0 = q := rfl
        -- the decomposition of `s` along the eventually periodic forced path
        have hdecomp : ∀ s : ℕ, a ≤ s → ∃ m j : ℕ, j < d ∧ s = a + d * m + j := by
          intro s hs
          have hdm : d * ((s - a) / d) + (s - a) % d = s - a := Nat.div_add_mod _ _
          exact ⟨(s - a) / d, (s - a) % d, Nat.mod_lt _ hdpos, by omega⟩
        have hwordper : ∀ m j : ℕ, loopWord M nxt q (a + d * m + j)
            = loopWord M nxt q a ++ loopPow (loopWord M nxt (loopState M nxt q a) d) m
              ++ loopWord M nxt (loopState M nxt q a) j := by
          intro m j
          rw [loopWord_add, loopWord_period hper m, loopState_period hper m]
        rcases loopWord_decomp M nxt q w 0 with ⟨s, hs⟩ | ⟨s, b, z, hb, hz⟩
        · -- the word follows the forced path all the way
          rw [hstate0] at hs
          by_cases hsa : s < a
          · exact ⟨constPat (loopWord M nxt q s),
              List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
                (List.mem_map_of_mem (List.mem_range.mpr hsa)))),
              fun _ => 0, by rw [chainWord_constPat, hs]⟩
          · obtain ⟨m, j, hj, rfl⟩ := hdecomp s (by omega)
            refine ⟨consLoopPat (loopWord M nxt q a) (loopWord M nxt (loopState M nxt q a) d)
                (constPat (loopWord M nxt (loopState M nxt q a) j)),
              List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
                (List.mem_map_of_mem (List.mem_range.mpr hj)))),
              fun i => if i = 0 then m else 0, ?_⟩
            rw [chainWord_consLoopPat, chainWord_constPat, hs, hwordper]
            simp
        · -- the word leaves the component
          rw [hstate0] at hz
          simp only [Nat.zero_add] at hb
          have hzacc : M.evalFrom (M.step (loopState M nxt q s) b) z ∈ M.accept := by
            rw [hz, M.evalFrom_of_append, evalFrom_loopWord] at hw
            exact hw
          obtain ⟨P, hP, c, hc⟩ := hFf _ (hexit s b hb) z hzacc
          by_cases hsa : s < a
          · refine ⟨consLoopPat (loopWord M nxt q s ++ [b]) [] P,
              List.mem_append_left _ (List.mem_append_right _ ?_),
              fun i => c (i - 1), ?_⟩
            · refine List.mem_flatMap.mpr ⟨s, List.mem_range.mpr hsa, ?_⟩
              refine List.mem_flatMap.mpr ⟨b, Finset.mem_toList.mpr (Finset.mem_univ b), ?_⟩
              exact List.mem_flatMap.mpr ⟨M.step (loopState M nxt q s) b,
                Finset.mem_toList.mpr (Finset.mem_univ _), List.mem_map_of_mem hP⟩
            · rw [chainWord_consLoopPat, loopPow_nil,
                show (fun i => c (i + 1 - 1)) = c from rfl, ← hc,
                hz]
              simp
          · obtain ⟨m, j, hj, rfl⟩ := hdecomp s (by omega)
            refine ⟨consLoopPat (loopWord M nxt q a) (loopWord M nxt (loopState M nxt q a) d)
                (prependPat (loopWord M nxt (loopState M nxt q a) j ++ [b]) P),
              List.mem_append_right _ ?_,
              fun i => if i = 0 then m else c (i - 1), ?_⟩
            · refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
              refine List.mem_flatMap.mpr ⟨b, Finset.mem_toList.mpr (Finset.mem_univ b), ?_⟩
              exact List.mem_flatMap.mpr ⟨M.step (loopState M nxt q (a + d * m + j)) b,
                Finset.mem_toList.mpr (Finset.mem_univ _), List.mem_map_of_mem hP⟩
            · rw [chainWord_consLoopPat, chainWord_prependPat,
                show (fun i => (if i + 1 = 0 then m else c (i + 1 - 1))) = c from
                  funext (fun i => by simp),
                ← hc, hz, hwordper]
              simp

end Cover

end RegGrowth

end Transducers.Exercises
