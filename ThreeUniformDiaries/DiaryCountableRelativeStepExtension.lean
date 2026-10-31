import ThreeUniformDiaries.DiaryCountableCoherentStrongEmbedding

/-!
# A relative one-step extension gate for countable diary unavoidability

An independently chosen embedding of every finite full support need not
produce a countable embedding.  The key obligation is to extend a
SPECIFIED support map without changing its images on earlier supports.

This file proves a genuine fusion statement: if one valid initial stage
exists and EVERY admissible stage map extends to the next stage while
fixing its old support, then there is one coherent infinite family.
The already verified coherent-stage gluing theorem consequently yields
an induced countable diary embedding preserving all nonmarker numerical
meets, with its leaves in the prescribed target range.

The relative extension hypothesis is deliberately explicit and remains
UNPROVED from finite strong flip absorption.  In particular, this
module is NOT a proof of unconditional countable-source unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finite stage map of the ACTUAL support of the countable diary.
The map is total on Nat for convenience, but all nonmarker laws are
restricted to the support of this stage. -/
structure AdmissibleCofinalDiaryStage
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (f : Nat → Nat) : Prop where
  ordered : ∀ u v : Nat,
    u ∈ countableDiaryFiniteSupport H m →
    v ∈ countableDiaryFiniteSupport H m →
    u < v → f u < f v
  marker_zero : f 0 = 0
  marker_one : f 1 = 1
  marker_two : f 2 = 2
  leaf_role : ∀ u : Nat,
    u ∈ countableDiaryFiniteSupport H m →
    IsLeaf H u → IsLeaf K (f u)
  one_split_role : ∀ u : Nat,
    u ∈ countableDiaryFiniteSupport H m →
    IsOneSplit H u → IsOneSplit K (f u)
  two_split_role : ∀ u : Nat,
    u ∈ countableDiaryFiniteSupport H m →
    IsTwoSplit H u → IsTwoSplit K (f u)
  induced_edge : ∀ a b c : Nat,
    a ∈ countableDiaryFiniteSupport H m →
    b ∈ countableDiaryFiniteSupport H m →
    c ∈ countableDiaryFiniteSupport H m →
    a < b → b < c →
    (H.edge a b c ↔ K.edge (f a) (f b) (f c))
  leaf_oneMeet : ∀ a b : Nat,
    a ∈ countableDiaryFiniteSupport H m →
    b ∈ countableDiaryFiniteSupport H m →
    IsLeaf H a → IsLeaf H b →
    K.oneMeetLevel (f a) (f b) = f (H.oneMeetLevel a b)
  leaf_twoMeet : ∀ a b c d : Nat,
    a ∈ countableDiaryFiniteSupport H m →
    b ∈ countableDiaryFiniteSupport H m →
    c ∈ countableDiaryFiniteSupport H m →
    d ∈ countableDiaryFiniteSupport H m →
    a < b → c < d →
    IsLeaf H a → IsLeaf H b →
    IsLeaf H c → IsLeaf H d →
    K.twoMeetLevel (f a) (f b) (f c) (f d) =
      f (H.twoMeetLevel a b c d)
  leaf_range : ∀ u : Nat,
    u ∈ countableDiaryFiniteSupport H m →
    IsLeaf H u → ∃ t : Nat, f u = F t

/-- Relative one-step extension produces a SINGLE genuinely coherent
sequence. Independent finite-stage existence does not suffice. -/
theorem exists_coherentDiaryStages_of_relative_extensions
    {H K : Ordered3Graph Nat} (DH : RoleDiary H)
    (F : Nat → Nat)
    (hInit : ∃ f : Nat → Nat, AdmissibleCofinalDiaryStage H K F 0 f)
    (hExtend : ∀ m : Nat, ∀ f : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F m f →
      ∃ g : Nat → Nat,
        AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
        (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
          g u = f u)) :
    ∃ P : CoherentCofinalDiarySupportMaps DH K,
      ∀ m u : Nat,
        u ∈ countableDiaryFiniteSupport H m →
        IsLeaf H u → ∃ t : Nat, P.map m u = F t := by
  classical
  let start : {f : Nat → Nat //
      AdmissibleCofinalDiaryStage H K F 0 f} :=
    ⟨Classical.choose hInit, Classical.choose_spec hInit⟩
  let step : ∀ m : Nat,
      (p : {f : Nat → Nat // AdmissibleCofinalDiaryStage H K F m f}) →
      {g : Nat → Nat //
        AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
        (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
          g u = p.1 u)} := by
    intro m p
    let h := hExtend m p.1 p.2
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  let stages : ∀ m : Nat,
      {f : Nat → Nat // AdmissibleCofinalDiaryStage H K F m f} :=
    Nat.rec start (fun m p => ⟨(step m p).1,(step m p).2.1⟩)
  have hAdjacent (m u : Nat)
      (hu : u ∈ countableDiaryFiniteSupport H m) :
      (stages (m + 1)).1 u = (stages m).1 u := by
    change (step m (stages m)).1 u = (stages m).1 u
    exact (step m (stages m)).2.2 u hu
  have hCoherent (m n : Nat) (hmn : m ≤ n)
      (u : Nat) (hu : u ∈ countableDiaryFiniteSupport H m) :
      (stages m).1 u = (stages n).1 u := by
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      have huN : u ∈ countableDiaryFiniteSupport H n :=
        (countableDiaryFiniteSupport_mono H m n hmn) hu
      exact ih.trans (hAdjacent n u huN).symm
  let P : CoherentCofinalDiarySupportMaps DH K := {
    map := fun m => (stages m).1
    coherent := by
      intro m n hmn u hu
      exact hCoherent m n hmn u hu
    ordered := by
      intro m u v hu hv huv
      exact (stages m).2.ordered u v hu hv huv
    marker_zero := by
      intro m
      exact (stages m).2.marker_zero
    marker_one := by
      intro m
      exact (stages m).2.marker_one
    marker_two := by
      intro m
      exact (stages m).2.marker_two
    leaf_role := by
      intro m u hu hLeaf
      exact (stages m).2.leaf_role u hu hLeaf
    one_split_role := by
      intro m u hu hOne
      exact (stages m).2.one_split_role u hu hOne
    two_split_role := by
      intro m u hu hTwo
      exact (stages m).2.two_split_role u hu hTwo
    induced_edge := by
      intro m a b c ha hb hc hab hbc
      exact (stages m).2.induced_edge a b c ha hb hc hab hbc
    leaf_oneMeet := by
      intro m a b ha hb hLa hLb
      exact (stages m).2.leaf_oneMeet a b ha hb hLa hLb
    leaf_twoMeet := by
      intro m a b c d ha hb hc hd hab hcd hLa hLb hLc hLd
      exact (stages m).2.leaf_twoMeet a b c d
        ha hb hc hd hab hcd hLa hLb hLc hLd
  }
  refine ⟨P,?_⟩
  intro m u hu hLeaf
  exact (stages m).2.leaf_range u hu hLeaf

/-- The precise positive conditional result:
relative one-step extension, for a specified generic-leaf range,
is sufficient for the countable-source lower-bound embedding.
This theorem does not establish its own extension hypothesis. -/
theorem exists_fullDiaryEmbedding_of_relative_extensions
    {H K : Ordered3Graph Nat} (DH : RoleDiary H)
    (DK : RoleDiary K) (F : Nat → Nat)
    (hInit : ∃ f : Nat → Nat, AdmissibleCofinalDiaryStage H K F 0 f)
    (hExtend : ∀ m : Nat, ∀ f : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F m f →
      ∃ g : Nat → Nat,
        AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
        (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
          g u = f u)) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  obtain ⟨P,hRange⟩ :=
    exists_coherentDiaryStages_of_relative_extensions DH F hInit hExtend
  exact P.exists_full_embedding_in_range DK F hRange

end DiaryLeafPriority
end ThreeUniformDiaries
