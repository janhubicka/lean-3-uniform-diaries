import ThreeUniformDiaries.DiaryCountableRelativeStepExtension

/-!
# The empty-leaf support is canonical: remove the redundant fusion base hypothesis

The first canonical finite support of a countable full diary contains
only marker vertices 0,1,2. The only increasing marker triple is
(0,1,2), which is forbidden by the (E1)--(E5) permitted-edge axiom.
Consequently the literal identity map is an admissible initial stage
for ANY prescribed leaf range.

Thus the conditional countable-source fusion theorem has just one
nontrivial hypothesis: *every* admissible finite stage must admit
a relative successor fixing the old support. We DO NOT prove that
extension hypothesis here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- With no genuine selected leaves, all generators vanish: the
stage-zero support is exactly the three distinguished markers. -/
theorem countableDiaryFiniteSupport_zero_eq
    (H : Ordered3Graph Nat) :
    countableDiaryFiniteSupport H 0 = Finset.range 3 := by
  classical
  have hEmpty : countableDiaryLeafPrefix H 0 = ∅ := by
    simp [countableDiaryLeafPrefix]
  simp [countableDiaryFiniteSupport, finiteLeafMeetSupport,
    hEmpty, finiteOneMeetSupport, finiteTwoMeetSupport,
    finiteOrderedLeafPairs]

/-- Every full diary forbids the only increasing all-marker triple. -/
theorem RoleDiary.marker_triple_zero_one_two_false
    {H : Ordered3Graph Nat} (D : RoleDiary H) :
    ¬ H.edge 0 1 2 := by
  intro he
  have hshape := D.permitted_edge 0 1 2 he
  simp [PermittedDiaryEdge, IsLeaf, IsOneSplit, IsTwoSplit] at hshape

/-- The stage-zero identity is admissible regardless of the
prescribed leaf range: no genuine source leaves are present. -/
theorem AdmissibleCofinalDiaryStage.marker_base
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F : Nat → Nat) :
    AdmissibleCofinalDiaryStage H K F 0 (fun u => u) := by
  have hSmall (u : Nat)
      (hu : u ∈ countableDiaryFiniteSupport H 0) : u < 3 := by
    rw [countableDiaryFiniteSupport_zero_eq] at hu
    exact Finset.mem_range.mp hu
  refine {
    ordered := ?_
    marker_zero := rfl
    marker_one := rfl
    marker_two := rfl
    leaf_role := ?_
    one_split_role := ?_
    two_split_role := ?_
    induced_edge := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
    leaf_range := ?_
  }
  · intro u v _ _ huv
    exact huv
  · intro u hu hLeaf
    have hs := hSmall u hu
    have h3 := hLeaf.1
    omega
  · intro u hu hSplit
    have hs := hSmall u hu
    have h3 := hSplit.1
    omega
  · intro u hu hSplit
    have hs := hSmall u hu
    have h3 := hSplit.1
    omega
  · intro a b c ha hb hc hab hbc
    have haSmall := hSmall a ha
    have hbSmall := hSmall b hb
    have hcSmall := hSmall c hc
    have ha0 : a = 0 := by omega
    have hb1 : b = 1 := by omega
    have hc2 : c = 2 := by omega
    subst a
    subst b
    subst c
    have hSource := DH.marker_triple_zero_one_two_false
    have hTarget := DK.marker_triple_zero_one_two_false
    tauto
  · intro a b ha _ hLeaf _
    have hs := hSmall a ha
    have h3 := hLeaf.1
    omega
  · intro a b c d ha _ _ _ _ _ hLeaf _ _ _
    have hs := hSmall a ha
    have h3 := hLeaf.1
    omega
  · intro u hu hLeaf
    have hs := hSmall u hu
    have h3 := hLeaf.1
    omega

/-- The relative extension principle alone suffices for coherent
countable stages: the initial stage need not be assumed. -/
theorem exists_coherentDiaryStages_of_relative_extension
    {H K : Ordered3Graph Nat} (DH : RoleDiary H)
    (DK : RoleDiary K) (F : Nat → Nat)
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
  exact exists_coherentDiaryStages_of_relative_extensions DH F
    ⟨fun u => u, AdmissibleCofinalDiaryStage.marker_base DH DK F⟩ hExtend

/-- Countable induced unavoidability with all nonmarker numerical
meets would follow from a single relative extension principle.
This is still CONDITIONAL: the extension hypothesis is open. -/
theorem exists_fullDiaryEmbedding_of_relative_extension
    {H K : Ordered3Graph Nat} (DH : RoleDiary H)
    (DK : RoleDiary K) (F : Nat → Nat)
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
  exact exists_fullDiaryEmbedding_of_relative_extensions
    DH DK F ⟨fun u => u, AdmissibleCofinalDiaryStage.marker_base DH DK F⟩
    hExtend

end DiaryLeafPriority
end ThreeUniformDiaries
