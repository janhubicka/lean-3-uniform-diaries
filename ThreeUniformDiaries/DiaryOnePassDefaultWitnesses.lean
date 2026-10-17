import ThreeUniformDiaries.DiaryOnePassFiniteSchedule

/-!
# Every selected child has a distinct realised default witness

The static one-pass algorithm gives one positive split bit to every
realised source singleton/pair germ except a chosen default germ in
each original type parent. The new V1/V2 witness proof requires
a NEGATIVE child in the SAME original parent as every selected
positive child. This is not obtained just by finiteness of the
type alphabets: the default child must itself be realised.

We prove a list-level invariant of least-by-rank selection:
a nonempty finite list yields a member of that list as its default.
For singleton germs, the terminal germ (when present) takes priority;
otherwise the source-lex least realised normal germ is selected.

For pair germs the first realised member of the finite fibre is
the default. Consequently every selected child has a DIFFERENT
default child of its own parent, both actually realised in the
source. These are the exact class witnesses needed at newly
inserted split vertices, with no S1/S2 hypotheses.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

private theorem foldl_smallerOneGerm_result_mem
    (m : Nat) (xs : List (OneGermSpace m)) :
    ∀ acc out,
      xs.foldl (chooseSmallerOneGerm m) acc = some out →
      acc = some out ∨ out ∈ xs := by
  induction xs with
  | nil =>
    intro acc out h
    exact Or.inl (by simpa using h)
  | cons g tail ih =>
    intro acc out h
    have htail :
        (chooseSmallerOneGerm m acc g) = some out ∨
          out ∈ tail := by
      apply ih (chooseSmallerOneGerm m acc g) out
      simpa only [List.foldl_cons] using h
    rcases htail with hchoice | hmem
    · cases acc with
      | none =>
        have heq : g = out :=
          Option.some.inj (by
            simpa [chooseSmallerOneGerm] using hchoice)
        exact Or.inr (by simp [heq])
      | some prev =>
        by_cases hlt :
          oneGermBinaryRank m g < oneGermBinaryRank m prev
        · have heq : g = out :=
            Option.some.inj (by
              simpa [chooseSmallerOneGerm, hlt] using hchoice)
          exact Or.inr (by simp [heq])
        · have heq : prev = out :=
            Option.some.inj (by
              simpa [chooseSmallerOneGerm, hlt] using hchoice)
          exact Or.inl (by simp [heq])
    · exact Or.inr (by simp [hmem])

private theorem foldl_smallerOneGerm_some
    (m : Nat) (xs : List (OneGermSpace m))
    (g : OneGermSpace m) :
    ∃ h, xs.foldl (chooseSmallerOneGerm m) (some g) =
      some h := by
  induction xs generalizing g with
  | nil =>
    exact ⟨g,rfl⟩
  | cons x tail ih =>
    by_cases hlt :
      oneGermBinaryRank m x < oneGermBinaryRank m g
    · simpa [List.foldl_cons,chooseSmallerOneGerm,hlt] using (ih x)
    · simpa [List.foldl_cons,chooseSmallerOneGerm,hlt] using (ih g)

/-- On a nonempty list the selected least-by-rank normal child
is itself an ACTUAL member, never a fabricated or empty child. -/
theorem leastOneGermByRank_realised
    (m : Nat) (xs : List (OneGermSpace m)) (hne : xs ≠ []) :
    ∃ h, h ∈ xs ∧ leastOneGermByRank m xs = some h := by
  cases xs with
  | nil =>
    exact False.elim (hne rfl)
  | cons g tail =>
    obtain ⟨h,hres⟩ := foldl_smallerOneGerm_some m tail g
    have hchosen : leastOneGermByRank m (g :: tail) = some h := by
      simpa [leastOneGermByRank,List.foldl_cons,
        chooseSmallerOneGerm] using hres
    have hmemCase :=
      foldl_smallerOneGerm_result_mem m (g :: tail)
        none h (by simpa only [leastOneGermByRank] using hchosen)
    rcases hmemCase with hnone | hmem
    · cases hnone
    · exact ⟨h,hmem,hchosen⟩

/-- The singleton default in any nonempty actual m-type fibre
is SOME genuinely realised child in precisely that fibre. -/
theorem oneDefaultGerm_realised_in_fibre
    (H : Ordered3Graph Nat) (m : Nat)
    (parent : OneCodeSpace m)
    (hne : (oneGermFibre H m parent).Nonempty) :
    ∃ h, h ∈ oneGermFibre H m parent ∧
      oneDefaultGerm H m parent = some h := by
  classical
  by_cases hterminal :
      oneGermCode H m m ∈ oneGermFibre H m parent
  · exact ⟨oneGermCode H m m,hterminal,
      by simp [oneDefaultGerm,hterminal]⟩
  · obtain ⟨g,hg⟩ := hne
    have hglist : g ∈ (oneGermFibre H m parent).toList :=
      Finset.mem_toList.mpr hg
    have hNonemptyList :
        (oneGermFibre H m parent).toList ≠ [] := by
      intro hnil
      simpa [hnil] using hglist
    obtain ⟨h,hhlist,hhchoose⟩ :=
      leastOneGermByRank_realised m
        (oneGermFibre H m parent).toList hNonemptyList
    have hhfib : h ∈ oneGermFibre H m parent :=
      Finset.mem_toList.mp hhlist
    exact ⟨h,hhfib,by
      simpa [oneDefaultGerm,hterminal] using hhchoose⟩

/-- The pair default is also a genuinely realised member of its
full two-type parent fibre. -/
theorem twoDefaultGerm_realised_in_fibre
    (H : Ordered3Graph Nat) (m : Nat)
    (parent : TwoCodeSpace m)
    (hne : (twoGermFibre H m parent).Nonempty) :
    ∃ h, h ∈ twoGermFibre H m parent ∧
      twoDefaultGerm H m parent = some h := by
  classical
  obtain ⟨g,hg⟩ := hne
  have hglist : g ∈ (twoGermFibre H m parent).toList :=
    Finset.mem_toList.mpr hg
  cases hlist : (twoGermFibre H m parent).toList with
  | nil =>
    simp [hlist] at hglist
  | cons h tail =>
    have hhlist : h ∈ (twoGermFibre H m parent).toList := by
      simp [hlist]
    exact ⟨h,Finset.mem_toList.mp hhlist,
      by simp [twoDefaultGerm,hlist]⟩

/-- Cached membership characterisation: a singleton fibre is just
the realised singleton germ set with one fixed parent code. -/
theorem oneGermFibre_mem_iff
    (H : Ordered3Graph Nat) (m : Nat)
    (parent : OneCodeSpace m) (g : OneGermSpace m) :
    g ∈ oneGermFibre H m parent ↔
      g ∈ realisedOneGerms H m ∧ g.1 = parent := by
  classical
  simp [oneGermFibre]

/-- The same fibre membership API for full ordered-pair germs. -/
theorem twoGermFibre_mem_iff
    (H : Ordered3Graph Nat) (m : Nat)
    (parent : TwoCodeSpace m) (g : TwoGermSpace m) :
    g ∈ twoGermFibre H m parent ↔
      g ∈ realisedTwoGerms H m ∧ g.1 = parent := by
  classical
  simp [twoGermFibre]

/-- Selected singleton membership records realisation plus
inequality with its own parent's default. -/
theorem selectedOneGerm_mem_iff
    (H : Ordered3Graph Nat) (m : Nat) (g : OneGermSpace m) :
    g ∈ selectedOneGerms H m ↔
      g ∈ realisedOneGerms H m ∧
      some g ≠ oneDefaultGerm H m g.1 := by
  classical
  simp [selectedOneGerms]

/-- Selected pair-germ membership has the identical structure. -/
theorem selectedTwoGerm_mem_iff
    (H : Ordered3Graph Nat) (m : Nat) (g : TwoGermSpace m) :
    g ∈ selectedTwoGerms H m ↔
      g ∈ realisedTwoGerms H m ∧
      some g ≠ twoDefaultGerm H m g.1 := by
  classical
  simp [selectedTwoGerms]

/-- For each SELECTED singleton child g, its parent contains a
different REALISED default child. This supplies negative witnesses
at every newly inserted 1-split. -/
theorem selectedOneGerm_has_distinct_default
    (H : Ordered3Graph Nat) (m : Nat)
    (g : OneGermSpace m) (hg : g ∈ selectedOneGerms H m) :
    ∃ h, h ∈ realisedOneGerms H m ∧ h.1 = g.1 ∧
      h ≠ g ∧ oneDefaultGerm H m g.1 = some h := by
  classical
  obtain ⟨hreal,hneq⟩ :=
    (selectedOneGerm_mem_iff H m g).mp hg
  have hgfib : g ∈ oneGermFibre H m g.1 :=
    (oneGermFibre_mem_iff H m g.1 g).mpr ⟨hreal,rfl⟩
  obtain ⟨h,hhfib,hdef⟩ :=
    oneDefaultGerm_realised_in_fibre H m g.1 ⟨g,hgfib⟩
  obtain ⟨hhmem,hhparent⟩ :=
    (oneGermFibre_mem_iff H m g.1 h).mp hhfib
  have hdistinct : h ≠ g := by
    intro heq
    subst h
    exact hneq hdef.symm
  exact ⟨h,hhmem,hhparent,hdistinct,hdef⟩

/-- For each SELECTED full-pair child g, its same-parent default
is REALISED and distinct, including capped terminal-pair germs. -/
theorem selectedTwoGerm_has_distinct_default
    (H : Ordered3Graph Nat) (m : Nat)
    (g : TwoGermSpace m) (hg : g ∈ selectedTwoGerms H m) :
    ∃ h, h ∈ realisedTwoGerms H m ∧ h.1 = g.1 ∧
      h ≠ g ∧ twoDefaultGerm H m g.1 = some h := by
  classical
  obtain ⟨hreal,hneq⟩ :=
    (selectedTwoGerm_mem_iff H m g).mp hg
  have hgfib : g ∈ twoGermFibre H m g.1 :=
    (twoGermFibre_mem_iff H m g.1 g).mpr ⟨hreal,rfl⟩
  obtain ⟨h,hhfib,hdef⟩ :=
    twoDefaultGerm_realised_in_fibre H m g.1 ⟨g,hgfib⟩
  obtain ⟨hhmem,hhparent⟩ :=
    (twoGermFibre_mem_iff H m g.1 h).mp hhfib
  have hdistinct : h ≠ g := by
    intro heq
    subst h
    exact hneq hdef.symm
  exact ⟨h,hhmem,hhparent,hdistinct,hdef⟩

end DiaryLeafPriority
end ThreeUniformDiaries
