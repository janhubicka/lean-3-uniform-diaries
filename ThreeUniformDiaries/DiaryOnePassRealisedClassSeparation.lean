import ThreeUniformDiaries.DiaryOnePassFiniteSchedule

/-!
# Exactly separating realised one-pass germ children by selected events

This is a crucial actual-source bridge from the finite one-hot
combinatorics to the corrected pre-diary completion algorithm.

At original cut m, the selected event classes are all realised
singleton (or full ordered-pair) germ children of each old parent,
EXCEPT one default child. Consequently two realised germ children
with the SAME parent have identical membership bits at every
selected class if and ONLY if they are the same germ.

The proof works for the actual finite original singleton/full pair
codes on countable sources, and is independent of the source S1/S2.
In particular it covers the capped terminal pair child.
This module does not yet assert exact target edge reflection at the
event positions or the global type-transport induction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- General finite one-hot separation with one omitted default
class in each parent: the default is detected by its all-zero
selected-class vector. This is a reusable statement independent
of any hypergraph or ordering of event positions. -/
theorem realised_children_detected_by_selected_bits
    {α β : Type*}
    (members : Finset α) (parent : α → β)
    (default : β → Option α)
    (g h : α) (hg : g ∈ members) (hh : h ∈ members)
    (hp : parent g = parent h)
    (hbits : ∀ c ∈ members.filter
      (fun c => some c ≠ default (parent c)), (g = c ↔ h = c)) :
    g = h := by
  classical
  by_contra hneq
  by_cases hgselected :
      g ∈ members.filter (fun c => some c ≠ default (parent c))
  · have h := (hbits g hgselected).mp rfl
    exact hneq h
  · have hgdefault : some g = default (parent g) := by
      by_contra hd
      exact hgselected (Finset.mem_filter.mpr ⟨hg, hd⟩)
    have hhselected :
        h ∈ members.filter (fun c => some c ≠ default (parent c)) := by
      apply Finset.mem_filter.mpr
      refine ⟨hh, ?_⟩
      intro hhdefault
      have hsame : some g = some h := by
        calc
          some g = default (parent g) := hgdefault
          _ = default (parent h) := congrArg default hp
          _ = some h := hhdefault.symm
      exact hneq (Option.some.inj hsame)
    have h := (hbits h hhselected).mpr rfl
    exact hneq h

/-- The finite selected 1-type events distinguish EXACTLY the
realised singleton germ children in each old 1-type parent.
No terminal/normal case is omitted. -/
theorem realised_oneGerm_eq_iff_selected_bits
    (H : Ordered3Graph Nat) (m : Nat)
    (g h : OneGermSpace m)
    (hg : g ∈ realisedOneGerms H m)
    (hh : h ∈ realisedOneGerms H m)
    (hp : g.1 = h.1) :
    (∀ c ∈ selectedOneGerms H m, (g = c ↔ h = c)) ↔
      g = h := by
  classical
  constructor
  · intro hbits
    apply realised_children_detected_by_selected_bits
      (realisedOneGerms H m) (fun g => g.1)
      (oneDefaultGerm H m) g h hg hh hp
    intro c hc
    apply hbits c
    simpa [selectedOneGerms] using hc
  · intro heq
    subst h
    intro c hc
    rfl

/-- Full ordered-pair germ children are also detected by the
selected 2-type event membership vector, INCLUDING capped terminal
pairs whose first member equals original m. -/
theorem realised_twoGerm_eq_iff_selected_bits
    (H : Ordered3Graph Nat) (m : Nat)
    (g h : TwoGermSpace m)
    (hg : g ∈ realisedTwoGerms H m)
    (hh : h ∈ realisedTwoGerms H m)
    (hp : g.1 = h.1) :
    (∀ c ∈ selectedTwoGerms H m, (g = c ↔ h = c)) ↔
      g = h := by
  classical
  constructor
  · intro hbits
    apply realised_children_detected_by_selected_bits
      (realisedTwoGerms H m) (fun g => g.1)
      (twoDefaultGerm H m) g h hg hh hp
    intro c hc
    apply hbits c
    simpa [selectedTwoGerms] using hc
  · intro heq
    subst h
    intro c hc
    rfl

/-- Concrete version for two actual source leaves in the same
old singleton parent. Equality of their finite selected-class
vectors is EXACTLY equality of their terminal/normal germs. -/
theorem source_oneGerm_eq_iff_selected_bits
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hparent : oneCode H m u = oneCode H m v) :
    (∀ c ∈ selectedOneGerms H m,
      (oneGermCode H m u = c ↔ oneGermCode H m v = c)) ↔
      oneGermCode H m u = oneGermCode H m v := by
  classical
  have hgu : oneGermCode H m u ∈ realisedOneGerms H m := by
    simp only [realisedOneGerms, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨u, hu, hmu, rfl⟩
  have hgv : oneGermCode H m v ∈ realisedOneGerms H m := by
    simp only [realisedOneGerms, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨v, hv, hmv, rfl⟩
  have hp : (oneGermCode H m u).1 = (oneGermCode H m v).1 := by
    simpa only [oneGermCode] using hparent
  exact realised_oneGerm_eq_iff_selected_bits H m
    (oneGermCode H m u) (oneGermCode H m v) hgu hgv hp

/-- Concrete full-pair version: no pair class information is
lost by leaving exactly one default selected-event bit at zero. -/
theorem source_twoGerm_eq_iff_selected_bits
    (H : Ordered3Graph Nat) (m u v a b : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hmu : m ≤ u) (huv : u < v)
    (hma : m ≤ a) (hab : a < b)
    (hparent : twoCode H m u v = twoCode H m a b) :
    (∀ c ∈ selectedTwoGerms H m,
      (twoGermCode H m u v = c ↔ twoGermCode H m a b = c)) ↔
      twoGermCode H m u v = twoGermCode H m a b := by
  classical
  have hgu : twoGermCode H m u v ∈ realisedTwoGerms H m := by
    simp only [realisedTwoGerms, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨u, v, hu, hv, hmu, huv, rfl⟩
  have hgv : twoGermCode H m a b ∈ realisedTwoGerms H m := by
    simp only [realisedTwoGerms, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨a, b, ha, hb, hma, hab, rfl⟩
  have hp : (twoGermCode H m u v).1 = (twoGermCode H m a b).1 := by
    simpa only [twoGermCode] using hparent
  exact realised_twoGerm_eq_iff_selected_bits H m
    (twoGermCode H m u v) (twoGermCode H m a b) hgu hgv hp

end DiaryLeafPriority
end ThreeUniformDiaries
