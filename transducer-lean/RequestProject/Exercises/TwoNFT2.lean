/-
The second half of the exercise `exer:2nft` of the chapter *Two-way transducers*
(`2dfa.tex`) of *Transducers* (M. Bojańczyk): the second nondeterministic model
of a two-way transducer is not contained in the first one.

The two models are the ones of `RequestProject/Exercises/TwoNFT.lean`, where the
first half of the exercise — that the first model is not contained in the second
— is proved.  The witness is the author's relation

  `{(aⁿ, v v) : v ∈ {a, b}ⁿ}`,

here with the input alphabet `Unit` and the output alphabet `Bool`
(`Transducers.Exercises.dupRel`).  It belongs to the second model, because the
labelling of the input by `Bool` is exactly the string `v`, which a
deterministic two-way transducer can then write twice; and it does not belong to
the first model, by the author's cut-and-paste argument: there are `2ⁿ` strings
`v` but only linearly many configurations, so two different `v₁ ≠ v₂` give
accepting runs that agree at the moment when the first half of the output has
been produced, and the two runs can be spliced into an accepting run whose
output is `v₁ v₂`.

One point that the solution passes over has to be dealt with: a single
transition may produce several output letters, so a run cannot in general be cut
after *exactly* `n` output letters.  It is cut instead at the first moment when
at least `n` letters have been produced (`TwoWayN.reachesN_cut`); the number of
extra letters is then at most the length `K` of the longest output of a
transition, and the pigeonhole is applied to the pair consisting of the
configuration and those extra letters, which is enough for the splicing to go
through.
-/
import RequestProject.Exercises.TwoNFT

namespace Transducers
namespace Exercises

/-! ## The relation of the counterexample -/

/-- The relation `{(aⁿ, v v) : v ∈ {a, b}ⁿ}` of the solution, with the input
alphabet `Unit` and the output alphabet `Bool`. -/
def dupRel (w : List Unit) (v : List Bool) : Prop :=
  ∃ u : List Bool, u.length = w.length ∧ v = u ++ u

/-! ## The relation belongs to the second model -/

lemma isRegular_univ {T : Type} : Language.IsRegular (Set.univ : Language T) := by
  refine ⟨Unit, inferInstance, ⟨fun _ _ => (), (), Set.univ⟩, ?_⟩
  ext w; simp [DFA.accepts, DFA.acceptsFrom]

/-- Writing the second component of a labelled input twice is a deterministic
two-way transducer: it is the map lifting of duplication, precomposed and
postcomposed with letter-to-letter maps. -/
lemma isTwoWay_dup2 : IsTwoWay (fun z : List (Unit × Bool) =>
    (z.map Prod.snd) ++ (z.map Prod.snd)) := by
  have h1 := isTwoWay_mapLift_dup Bool
  have h2 := isTwoWay_precomp_map h1 (fun p : Unit × Bool => some p.2)
  have h3 := isTwoWay_postMap h2 (fun o : Option Bool => o.getD false)
  have key : (fun w : List (Unit × Bool) => List.map (fun o : Option Bool => o.getD false)
      (mapLift (fun x : List Bool => x ++ x) (List.map (fun p : Unit × Bool => some p.2) w)))
      = fun z : List (Unit × Bool) => (z.map Prod.snd) ++ (z.map Prod.snd) := by
    funext z
    have hz : List.map (fun p : Unit × Bool => some p.2) z = (z.map Prod.snd).map some := by
      simp [List.map_map]
    rw [hz, mapLift_map_some]
    simp [List.map_map, Function.comp_def]
  rwa [key] at h3

/-- `dupRel` belongs to the second model: the auxiliary alphabet is `Bool`, every
labelling is valid, and the deterministic two-way transducer writes the
labelling twice. -/
theorem isTwoNFT₂_dupRel : IsTwoNFT₂ dupRel := by
  obtain ⟨Q, hQ, M, hM⟩ := isTwoWay_dup2
  refine ⟨Bool, inferInstance, Q, hQ, M, Set.univ, isRegular_univ, ?_⟩
  intro w v
  constructor
  · rintro ⟨u, hlen, rfl⟩
    refine ⟨w.zip u, ?_, trivial, ?_⟩
    · simp [List.map_fst_zip, hlen.ge]
    · have h1 : (w.zip u).map Prod.snd = u := by
        simp [List.map_snd_zip, hlen.le]
      simpa [h1] using hM (w.zip u)
  · rintro ⟨z, hz, -, hc⟩
    have := TwoWay.computes_unique hc (hM z)
    exact ⟨z.map Prod.snd, by simp [← hz], this⟩

/-! ## Runs of a nondeterministic two-way transducer -/

namespace TwoWayN

variable {A B Q : Type}

lemma reachesN_trans {M : TwoWayN A B Q} {c c' c'' : Cfg A Q} {o o' : List B}
    (h : M.ReachesN c o c') (h' : M.ReachesN c' o' c'') : M.ReachesN c (o ++ o') c'' := by
  induction h with
  | refl c => simpa using h'
  | step hs _ ih => rw [List.append_assoc]; exact TwoWayN.ReachesN.step hs (ih h')

/-- A configuration of a run on the input string `w`: the two halves of the tape
concatenate to `w`. -/
def CfgOn (w : List A) : Cfg A Q → Prop
  | Cfg.conf u _ v => u ++ v = w
  | Cfg.halt => True

lemma stepN_cfgOn {M : TwoWayN A B Q} {w : List A} {c c' : Cfg A Q} {o : List B}
    (h : M.StepN c o c') (hc : CfgOn w c) : CfgOn w c' := by
  cases h with
  | halt => trivial
  | @right u v a q q' o hv _ =>
      simp only [CfgOn] at hc ⊢
      cases v with
      | nil => simp at hv
      | cons b v' =>
          simp only [List.head?_cons, Option.some.injEq] at hv
          subst hv
          simpa using hc
  | @left u v a q q' o hu _ =>
      simp only [CfgOn] at hc ⊢
      have hd : u.dropLast ++ [a] = u := List.dropLast_append_getLast? a hu
      calc u.dropLast ++ a :: v = (u.dropLast ++ [a]) ++ v := by simp
        _ = u ++ v := by rw [hd]
        _ = w := hc

lemma reachesN_cfgOn {M : TwoWayN A B Q} {w : List A} {c c' : Cfg A Q} {o : List B}
    (h : M.ReachesN c o c') (hc : CfgOn w c) : CfgOn w c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (stepN_cfgOn hs hc)

/-- The output string of a transition. -/
def transOut : List B ⊕ (Q × List B × Bool) → List B
  | Sum.inl o => o
  | Sum.inr (_, o, _) => o

/-- A transducer with finitely many states, over a finite input alphabet and
with finite transition sets, produces boundedly many output letters per step. -/
lemma exists_step_bound [Finite A] [Finite Q] (M : TwoWayN A B Q)
    (hfin : ∀ l q r, (M.step l q r).Finite) :
    ∃ K : ℕ, ∀ (c c' : Cfg A Q) (o : List B), M.StepN c o c' → o.length ≤ K := by
  classical
  set S : Set (List B ⊕ (Q × List B × Bool)) :=
    ⋃ x : Option A × Q × Option A, M.step x.1 x.2.1 x.2.2 with hS
  have hSfin : S.Finite := Set.finite_iUnion (fun x => hfin x.1 x.2.1 x.2.2)
  have himg : ((fun t => (transOut t).length) '' S).Finite := hSfin.image _
  obtain ⟨K, hKmem⟩ := himg.bddAbove
  refine ⟨K, ?_⟩
  intro c c' o h
  have hmem : ∀ t ∈ S, (transOut t).length ≤ K := fun t ht => hKmem ⟨t, ht, rfl⟩
  cases h with
  | @halt u v q o hstep =>
      exact hmem (Sum.inl o) (Set.mem_iUnion.2 ⟨(u.getLast?, q, v.head?), hstep⟩)
  | @right u v a q q' o hv hstep =>
      exact hmem (Sum.inr (q', o, true)) (Set.mem_iUnion.2 ⟨(u.getLast?, q, some a), hstep⟩)
  | @left u v a q q' o hu hstep =>
      exact hmem (Sum.inr (q', o, false)) (Set.mem_iUnion.2 ⟨(some a, q, v.head?), hstep⟩)

/-- A run can be cut at the first moment when at least `n` output letters have
been produced; the prefix of the output then has length between `n` and
`n + K`. -/
lemma reachesN_cut {M : TwoWayN A B Q} {K : ℕ}
    (hK : ∀ (c c' : Cfg A Q) (o : List B), M.StepN c o c' → o.length ≤ K)
    {c d : Cfg A Q} {o : List B} (h : M.ReachesN c o d) :
    ∀ n ≤ o.length, ∃ (c' : Cfg A Q) (o₁ o₂ : List B),
      o = o₁ ++ o₂ ∧ M.ReachesN c o₁ c' ∧ M.ReachesN c' o₂ d ∧
        n ≤ o₁.length ∧ o₁.length ≤ n + K := by
  induction h with
  | refl c =>
      intro n hn
      simp only [List.length_nil, Nat.le_zero] at hn
      subst hn
      exact ⟨c, [], [], rfl, ReachesN.refl _, ReachesN.refl _, by simp, by simp⟩
  | @step c c' c'' a o' hs hr ih =>
      intro n hn
      by_cases hcase : n ≤ a.length
      · refine ⟨c', a, o', rfl, ?_, hr, ?_, ?_⟩
        · simpa using ReachesN.step hs (ReachesN.refl c')
        · simpa using hcase
        · have := hK _ _ _ hs
          omega
      · have hn' : n - a.length ≤ o'.length := by
          simp only [List.length_append] at hn
          omega
        obtain ⟨c₀, o₁, o₂, hcat, h1, h2, hl1, hl2⟩ := ih (n - a.length) hn'
        refine ⟨c₀, a ++ o₁, o₂, by rw [List.append_assoc, ← hcat], ?_, h2, ?_, ?_⟩
        · simpa using ReachesN.step hs h1
        · simp only [List.length_append]; omega
        · simp only [List.length_append]; omega

end TwoWayN

/-! ## Counting -/

lemma exists_two_pow_gt (a b : ℕ) : ∃ n : ℕ, a * (n + 1) + b < 2 ^ n := by
  refine ⟨2 * (3 * (a + b) + 1), ?_⟩
  set t := 3 * (a + b) + 1 with ht
  have ht1 : 1 ≤ t := by omega
  have h1 : a * (2 * t + 1) + b ≤ 3 * (a + b) * t := by nlinarith [ht1]
  have h2 : 3 * (a + b) * t < t * t := by nlinarith [ht1]
  have h3 : t < 2 ^ t := Nat.lt_two_pow_self
  have h4 : t * t < 2 ^ t * 2 ^ t := Nat.mul_lt_mul_of_lt_of_lt h3 h3
  have h5 : (2:ℕ) ^ t * 2 ^ t = 2 ^ (2 * t) := by rw [← pow_add]; ring_nf
  omega

lemma list_unit_eq (u : List Unit) : u = List.replicate u.length () := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      cases a
      rw [List.length_cons, List.replicate_succ]
      exact congrArg _ ih

variable {Q : Type}

/-- A code for the configurations of a run on the input `aⁿ`. -/
def cfgCode (n : ℕ) : Cfg Unit Q → Option (Fin (n + 1) × Q)
  | Cfg.conf u q _ => some (⟨min u.length n, Nat.lt_succ_of_le (min_le_right _ _)⟩, q)
  | Cfg.halt => none

lemma cfg_eq_of_code {n : ℕ} {c₁ c₂ : Cfg Unit Q}
    (h₁ : TwoWayN.CfgOn (List.replicate n ()) c₁)
    (h₂ : TwoWayN.CfgOn (List.replicate n ()) c₂)
    (h : cfgCode n c₁ = cfgCode n c₂) : c₁ = c₂ := by
  cases c₁ with
  | halt =>
      cases c₂ with
      | halt => rfl
      | conf u q v => simp [cfgCode] at h
  | conf u₁ q₁ v₁ =>
      cases c₂ with
      | halt => simp [cfgCode] at h
      | conf u₂ q₂ v₂ =>
          simp only [TwoWayN.CfgOn] at h₁ h₂
          have e₁ : u₁.length + v₁.length = n := by
            have := congrArg List.length h₁; simpa using this
          have e₂ : u₂.length + v₂.length = n := by
            have := congrArg List.length h₂; simpa using this
          simp only [cfgCode, Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
          have hu : u₁.length = u₂.length := by omega
          have hv : v₁.length = v₂.length := by omega
          have hu' : u₁ = u₂ := by
            rw [list_unit_eq u₁, list_unit_eq u₂, hu]
          have hv' : v₁ = v₂ := by
            rw [list_unit_eq v₁, list_unit_eq v₂, hv]
          rw [hu', hv', h.2]

/-- A code for the strings of length at most `K`. -/
def strCode (K : ℕ) (s : List Bool) : Fin (K + 1) × (Fin K → Bool) :=
  (⟨min s.length K, Nat.lt_succ_of_le (min_le_right _ _)⟩, fun i => s.getD i.val false)

lemma str_eq_of_code {K : ℕ} {s₁ s₂ : List Bool} (h₁ : s₁.length ≤ K) (h₂ : s₂.length ≤ K)
    (h : strCode K s₁ = strCode K s₂) : s₁ = s₂ := by
  simp only [strCode, Prod.mk.injEq, Fin.mk.injEq] at h
  have hlen : s₁.length = s₂.length := by
    have := h.1
    omega
  refine List.ext_getElem hlen ?_
  intro i hi₁ hi₂
  have hiK : i < K := lt_of_lt_of_le hi₁ h₁
  have := congrFun h.2 ⟨i, hiK⟩
  simpa [List.getD_eq_getElem, hi₁, hi₂] using this

/-! ## The relation does not belong to the first model -/

/-- The author's cut-and-paste argument: `dupRel` is not computed by a
nondeterministic two-way transducer of the first kind. -/
theorem not_isTwoNFT₁_dupRel : ¬ IsTwoNFT₁ dupRel := by
  classical
  rintro ⟨Q, hQ, M, hfin, hR⟩
  haveI : Finite Q := hQ
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨K, hK⟩ := TwoWayN.exists_step_bound M hfin
  obtain ⟨n, hn⟩ :=
    exists_two_pow_gt (Fintype.card Q * ((K + 1) * 2 ^ K)) ((K + 1) * 2 ^ K)
  set w : List Unit := List.replicate n () with hw
  set c₀ : Cfg Unit Q := Cfg.conf [] M.init w with hc₀
  have hc₀on : TwoWayN.CfgOn w c₀ := by simp [TwoWayN.CfgOn, hc₀]
  have hall : ∀ f : Fin n → Bool, ∃ (c : Cfg Unit Q) (o₁ o₂ : List Bool),
      List.ofFn f ++ List.ofFn f = o₁ ++ o₂ ∧ M.ReachesN c₀ o₁ c ∧
        M.ReachesN c o₂ Cfg.halt ∧ n ≤ o₁.length ∧ o₁.length ≤ n + K := by
    intro f
    have hd : dupRel w (List.ofFn f ++ List.ofFn f) := ⟨List.ofFn f, by simp [hw], rfl⟩
    have hre : M.ReachesN c₀ (List.ofFn f ++ List.ofFn f) Cfg.halt := (hR _ _).1 hd
    have hlen : n ≤ (List.ofFn f ++ List.ofFn f).length := by simp
    exact TwoWayN.reachesN_cut hK hre n hlen
  choose C O₁ O₂ hcat hre₁ hre₂ hl₁ hl₂ using hall
  -- pigeonhole on the configuration and the extra output letters
  have hcard : Fintype.card (Option (Fin (n + 1) × Q) × (Fin (K + 1) × (Fin K → Bool)))
      < Fintype.card (Fin n → Bool) := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Fintype.card_fun,
      Fintype.card_bool]
    calc ((n + 1) * Fintype.card Q + 1) * ((K + 1) * 2 ^ K)
        = Fintype.card Q * ((K + 1) * 2 ^ K) * (n + 1) + (K + 1) * 2 ^ K := by ring
      _ < 2 ^ n := hn
  obtain ⟨f, g, hfg, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun f : Fin n → Bool => (cfgCode n (C f), strCode K ((O₁ f).drop n))) hcard
  apply hfg
  simp only [Prod.mk.injEq] at heq
  -- the two runs agree at the cut
  have hCf : TwoWayN.CfgOn w (C f) := TwoWayN.reachesN_cfgOn (hre₁ f) hc₀on
  have hCg : TwoWayN.CfgOn w (C g) := TwoWayN.reachesN_cfgOn (hre₁ g) hc₀on
  have hC : C f = C g := cfg_eq_of_code hCf hCg heq.1
  have hbf : ((O₁ f).drop n).length ≤ K := by
    have := hl₂ f; simp only [List.length_drop]; omega
  have hbg : ((O₁ g).drop n).length ≤ K := by
    have := hl₂ g; simp only [List.length_drop]; omega
  have hS : (O₁ f).drop n = (O₁ g).drop n := str_eq_of_code hbf hbg heq.2
  set s : List Bool := (O₁ f).drop n with hs
  -- the shape of the two prefixes
  have shape : ∀ h : Fin n → Bool, O₁ h = List.ofFn h ++ (O₁ h).drop n := by
    intro h
    have hlen : (List.ofFn h).length = n := by simp
    have h1 : O₁ h = (List.ofFn h ++ List.ofFn h).take (O₁ h).length := by
      conv_lhs => rw [show O₁ h = (O₁ h ++ O₂ h).take (O₁ h).length from (List.take_left).symm]
      rw [← hcat h]
    have h2 : (List.ofFn h ++ List.ofFn h).take (O₁ h).length
        = List.ofFn h ++ (List.ofFn h).take ((O₁ h).length - n) := by
      rw [List.take_append, hlen]
      congr 1
      exact List.take_of_length_le (by rw [hlen]; exact hl₁ h)
    have h3 : O₁ h = List.ofFn h ++ (List.ofFn h).take ((O₁ h).length - n) := h1.trans h2
    have h4 : (O₁ h).drop n = (List.ofFn h).take ((O₁ h).length - n) := by
      conv_lhs => rw [h3]
      exact List.drop_left' hlen
    rw [h4]
    exact h3
  have hOf : O₁ f = List.ofFn f ++ s := shape f
  have hOg : O₁ g = List.ofFn g ++ s := by rw [hS]; exact shape g
  -- the second half of the run for `g`
  have hgs : List.ofFn g = s ++ O₂ g := by
    have := hcat g
    rw [hOg, List.append_assoc] at this
    exact List.append_cancel_left this
  -- splicing
  have hsplice : M.ReachesN c₀ (O₁ f ++ O₂ g) Cfg.halt := by
    refine TwoWayN.reachesN_trans (hre₁ f) ?_
    rw [hC]; exact hre₂ g
  have hmem : dupRel w (O₁ f ++ O₂ g) := (hR _ _).2 hsplice
  obtain ⟨u, hulen, hueq⟩ := hmem
  have hcalc : O₁ f ++ O₂ g = List.ofFn f ++ List.ofFn g := by
    rw [hOf, List.append_assoc, ← hgs]
  rw [hcalc] at hueq
  have hun : u.length = n := by rw [hulen, hw]; simp
  have hfn : (List.ofFn f).length = u.length := by simp [hun]
  obtain ⟨hf1, hf2⟩ := List.append_inj hueq hfn
  exact List.ofFn_injective (hf1.trans hf2.symm)

/-! ## The exercise -/

/-- **Exercise `exer:2nft`, second half.**  The second nondeterministic model of
a two-way transducer is not contained in the first one: the relation
`{(aⁿ, v v) : v ∈ {a, b}ⁿ}` belongs to the second model and not to the first. -/
theorem exists_isTwoNFT₂_not_isTwoNFT₁ :
    ∃ R : List Unit → List Bool → Prop, IsTwoNFT₂ R ∧ ¬ IsTwoNFT₁ R :=
  ⟨dupRel, isTwoNFT₂_dupRel, not_isTwoNFT₁_dupRel⟩

end Exercises
end Transducers
