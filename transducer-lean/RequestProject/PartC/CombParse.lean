/-
Claim `claim:parsing-is-regular` of Section *Combinators* of *Transducers* (M. Bojańczyk).

The claim, used in the proof of Lemma `lem:distributivity-is-regular-under-string-representation`,
says that for every type `A` the set of strings over the eight-letter alphabet that represent an
element of `A` is a regular language.  The book proves it "by a straightforward induction on the
structure of the type", and that is what is done here: the language of representations is described
by a regular expression built from the languages of the components,

* `1`                     is represented by the one-word language `{1}`;
* `A × B`                 by `( · A · , · B · )`;
* `A + B`                 by `L · A  ∪  R · B`;
* `A*`                    by `[ · body · ]`, where the body of a list representation is either
                          empty or a representation of `A` followed by any number of blocks
                          `, · A`,

and the regular languages are closed under the operations used, by
`RequestProject/Common/RegLangClosure.lean` (concatenation, union and the Kleene star) and by
Mathlib.

The development of Part C parses a representation with the bracket counter of
`PartC/CombDepth.lean` rather than with an automaton built by recursion on the type, so this claim
is not what the transducers of the easy direction of Theorem `thm:regular-terms` actually use; it
is proved here for its own sake, as a numbered result of the book.
-/
import RequestProject.Common.RegLangClosure
import RequestProject.PartC.CombTypes

namespace Transducers

open Computability

/-! ## The three languages of the induction -/

/-- The language of the string representations of the elements of a type: the language of Claim
`claim:parsing-is-regular`. -/
def reprLang (A : Ty) : Language Sym8 := {w | ∃ a : A.Elt, A.repr a = w}

/-- The body of the representation of a list: the representations of its entries, separated by
commas. -/
def joinSepLang (A : Ty) : Language Sym8 := {w | ∃ l : List A.Elt, joinSep (l.map A.repr) = w}

/-- The representations of the entries of a list, each preceded by a comma. -/
def commaBlocksLang (A : Ty) : Language Sym8 := {w | ∃ l : List A.Elt, commaBlocks A l = w}

/-! ## Concatenation with a one-letter language -/

lemma mem_singleton_mul {c : Sym8} {L : Language Sym8} {w : List Sym8} :
    w ∈ ({[c]} : Language Sym8) * L ↔ ∃ v ∈ L, w = c :: v := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp h
    exact ⟨v, hv, by rw [show u = [c] from hu]; rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact Language.mem_mul.mpr ⟨[c], rfl, v, hv, rfl⟩

lemma mem_mul_singleton {c : Sym8} {L : Language Sym8} {w : List Sym8} :
    w ∈ L * ({[c]} : Language Sym8) ↔ ∃ u ∈ L, w = u ++ [c] := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp h
    exact ⟨u, hu, by rw [show v = [c] from hv]⟩
  · rintro ⟨u, hu, rfl⟩
    exact Language.mem_mul.mpr ⟨u, hu, [c], rfl, rfl⟩

/-! ## The regular expression of each type constructor -/

lemma reprLang_one : reprLang .one = ({[Sym8.one]} : Language Sym8) := by
  ext w
  constructor
  · rintro ⟨a, rfl⟩; rfl
  · intro hw
    exact ⟨(), by rw [show w = [Sym8.one] from hw]; exact Ty.repr_one ()⟩

lemma reprLang_prod (A B : Ty) :
    reprLang (.prod A B)
      = {[Sym8.lpar]} * (reprLang A * ({[Sym8.comma]} * (reprLang B * {[Sym8.rpar]}))) := by
  ext w
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine mem_singleton_mul.mpr ⟨_, Language.mem_mul.mpr ⟨A.repr a, ⟨a, rfl⟩, _,
      mem_singleton_mul.mpr ⟨_, mem_mul_singleton.mpr ⟨B.repr b, ⟨b, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  · intro hw
    obtain ⟨v, hv, rfl⟩ := mem_singleton_mul.mp hw
    obtain ⟨x, ⟨a, rfl⟩, y, hy, rfl⟩ := Language.mem_mul.mp hv
    obtain ⟨z, hz, rfl⟩ := mem_singleton_mul.mp hy
    obtain ⟨t, ⟨b, rfl⟩, rfl⟩ := mem_mul_singleton.mp hz
    exact ⟨(a, b), rfl⟩

lemma reprLang_sum (A B : Ty) :
    reprLang (.sum A B) = {[Sym8.left]} * reprLang A + {[Sym8.right]} * reprLang B := by
  ext w
  rw [Language.mem_add]
  constructor
  · rintro ⟨a | b, rfl⟩
    · exact Or.inl (mem_singleton_mul.mpr ⟨_, ⟨a, rfl⟩, rfl⟩)
    · exact Or.inr (mem_singleton_mul.mpr ⟨_, ⟨b, rfl⟩, rfl⟩)
  · rintro (hw | hw)
    · obtain ⟨v, ⟨a, rfl⟩, rfl⟩ := mem_singleton_mul.mp hw
      exact ⟨Sum.inl a, rfl⟩
    · obtain ⟨v, ⟨b, rfl⟩, rfl⟩ := mem_singleton_mul.mp hw
      exact ⟨Sum.inr b, rfl⟩

lemma reprLang_list (A : Ty) :
    reprLang (.list A) = {[Sym8.lbrack]} * (joinSepLang A * {[Sym8.rbrack]}) := by
  ext w
  constructor
  · rintro ⟨l, rfl⟩
    exact mem_singleton_mul.mpr
      ⟨_, mem_mul_singleton.mpr ⟨joinSep (l.map A.repr), ⟨l, rfl⟩, rfl⟩, rfl⟩
  · intro hw
    obtain ⟨v, hv, rfl⟩ := mem_singleton_mul.mp hw
    obtain ⟨u, ⟨l, rfl⟩, rfl⟩ := mem_mul_singleton.mp hv
    exact ⟨l, rfl⟩

/-- The blocks `, a` of a list representation are exactly the words of the Kleene star of the
language of one such block. -/
lemma commaBlocksLang_eq (A : Ty) :
    commaBlocksLang A = ({[Sym8.comma]} * reprLang A)∗ := by
  ext w
  constructor
  · rintro ⟨l, rfl⟩
    induction l with
    | nil => simpa using Language.nil_mem_kstar _
    | cons a l ih =>
        rw [commaBlocks_cons, show Sym8.comma :: (A.repr a ++ commaBlocks A l)
          = (Sym8.comma :: A.repr a) ++ commaBlocks A l from rfl]
        exact append_mem_kstar (mem_kstar_of_mem (mem_singleton_mul.mpr ⟨_, ⟨a, rfl⟩, rfl⟩)) ih
  · intro hw
    obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.mp hw
    clear hw
    induction S with
    | nil => exact ⟨[], rfl⟩
    | cons x S ih =>
        obtain ⟨l, hl⟩ := ih fun y hy => hS y (List.mem_cons_of_mem _ hy)
        obtain ⟨v, ⟨a, rfl⟩, rfl⟩ := mem_singleton_mul.mp (hS x List.mem_cons_self)
        exact ⟨a :: l, by rw [commaBlocks_cons, hl]; simp⟩

/-- The body of a list representation is either empty, or a representation followed by blocks. -/
lemma joinSepLang_eq (A : Ty) :
    joinSepLang A = 1 + reprLang A * commaBlocksLang A := by
  ext w
  rw [Language.mem_add]
  constructor
  · rintro ⟨l, rfl⟩
    cases l with
    | nil => exact Or.inl ((Language.mem_one _).mpr rfl)
    | cons a l =>
        refine Or.inr (Language.mem_mul.mpr ⟨A.repr a, ⟨a, rfl⟩, commaBlocks A l, ⟨l, rfl⟩, ?_⟩)
        rw [joinSep_cons, joinSepTail_eq_commaBlocks]
  · rintro (hw | hw)
    · exact ⟨[], by rw [(Language.mem_one _).mp hw]; rfl⟩
    · obtain ⟨u, ⟨a, rfl⟩, v, ⟨l, rfl⟩, rfl⟩ := Language.mem_mul.mp hw
      exact ⟨a :: l, by rw [joinSep_cons, joinSepTail_eq_commaBlocks]⟩

/-! ## The claim -/

private lemma isRegular_singletonLetter (c : Sym8) : ({[c]} : Language Sym8).IsRegular :=
  isRegular_singleton [c]

/-- **Claim `claim:parsing-is-regular`.**  For every type `A`, the strings over the eight-letter
alphabet that represent an element of `A` form a regular language. -/
theorem reprLang_isRegular : ∀ A : Ty, (reprLang A).IsRegular
  | .one => by rw [reprLang_one]; exact isRegular_singletonLetter _
  | .prod A B => by
      rw [reprLang_prod]
      exact isRegular_mul (isRegular_singletonLetter _)
        (isRegular_mul (reprLang_isRegular A)
          (isRegular_mul (isRegular_singletonLetter _)
            (isRegular_mul (reprLang_isRegular B) (isRegular_singletonLetter _))))
  | .sum A B => by
      rw [reprLang_sum]
      exact (isRegular_mul (isRegular_singletonLetter _) (reprLang_isRegular A)).add
        (isRegular_mul (isRegular_singletonLetter _) (reprLang_isRegular B))
  | .list A => by
      have hone : (1 : Language Sym8).IsRegular := by
        have := isRegular_singleton ([] : List Sym8)
        rwa [← Language.one_def] at this
      have hbody : (joinSepLang A).IsRegular := by
        rw [joinSepLang_eq, commaBlocksLang_eq]
        exact hone.add (isRegular_mul (reprLang_isRegular A)
          (isRegular_kstar (isRegular_mul (isRegular_singletonLetter _) (reprLang_isRegular A))))
      rw [reprLang_list]
      exact isRegular_mul (isRegular_singletonLetter _)
        (isRegular_mul hbody (isRegular_singletonLetter _))

end Transducers
