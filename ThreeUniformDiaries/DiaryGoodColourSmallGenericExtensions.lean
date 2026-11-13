import ThreeUniformDiaries.DiaryGoodColourOnePointGenericCopy
import ThreeUniformDiaries.DiaryChosenOldSupportSaturatedGoodColour

/-!
# Track A: chosen GOOD old-cut colour already solves generic stages n=0,1

English-first adversarial proof: 3-uniform-diaries PR #342.

Track D fixes ONE genuine old reserved support f and ONE anchored
complete oldStageTailCut colour c with cofinally late ACTUAL compatible
reserved immediate successors in the ORIGINAL arbitrary unordered F
range. Target VALUE cofinality implies SOURCE INDEX cofinality even
when F is not monotone or injective: all images of a finite source
index prefix have a finite maximum, so a larger target image must
come from outside that prefix.

For any finite G embedding stage whose source has n≤1 vertices,
there are NO ordered old pairs and thus NO required E5 edge/nonedge
tests when choosing its next vertex. Source-index cofinality of
this SAME anchored good colour supplies a legal new source index
above the literal existing stage bound.

The size-two generic extension is the FIRST new E5 constraint.
It is NOT established here. There is no all-n generic extension
property, no guaranteed good generic reservoir and no all-future
source-horizon persistent diary successor.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Cofinality of a predicate in the TARGET NUMERICAL VALUES F(t)
implies cofinality among ORIGINAL SOURCE indices t, even when F
is arbitrary (not monotone or injective). The finite initial
source image prefix is numerically bounded by Finset.sup. -/
theorem source_index_cofinal_of_target_value_cofinal
    (F : Nat → Nat) (C : Nat → Prop)
    (hTarget : ∀ M : Nat, ∃ t : Nat, M < F t ∧ C t) :
    ∀ B : Nat, ∃ t : Nat, B ≤ t ∧ C t := by
  classical
  intro B
  let M := (Finset.range B).sup F
  obtain ⟨t, hHigh, hColour⟩ := hTarget M
  refine ⟨t, ?_, hColour⟩
  by_contra hNot
  have ht : t < B := Nat.lt_of_not_ge hNot
  have hBound : F t ≤ M :=
    Finset.le_sup (f := F) (Finset.mem_range.mpr ht)
  omega

/-- A source-index cofinal colour gives the exact prescribed
next-generic-vertex finite edge/nonedge extension for EVERY
already induced coloured stage of size n≤1. No pair of old
vertices i<j exists at these sizes, so the required E5 table
is vacuous; no chosen old image needs to move. -/
theorem small_generic_extension_of_source_index_cofinal
    (G : GenericEnumerated3Graph)
    (C : Nat → Prop)
    (hCofinal : ∀ B : Nat, ∃ t : Nat, B ≤ t ∧ C t)
    {n : Nat} (hn : n ≤ 1)
    (s : FiniteGenericStage G G.graph n)
    (_hOld : ∀ i : Fin n, C (s.image i).val) :
    ∃ v : Nat, s.bound ≤ v ∧ C v ∧
      ∀ i j : Fin n, i < j →
        (G.graph.edge i.val j.val n ↔
          G.graph.edge (s.image i).val (s.image j).val v) := by
  obtain ⟨v, hBound, hColour⟩ := hCofinal s.bound
  refine ⟨v, hBound, hColour, ?_⟩
  intro i j hij
  have hImpossible : False := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  exact False.elim hImpossible

/-- An ACTUAL source/target role-diary pair, a genuine next source
leaf m with at least one old leaf, and an arbitrary ORIGINAL
unordered induced generic true-leaf range F admit one fixed
old RESERVED support map f and one full old-cut colour c such that:

(1) c has an ACTUAL compatible reserved immediate successor anchor;
(2) every finite increasing induced G-stage of size 0 or 1,
    all of whose indices are colour c, has a next G-index of
    colour c beyond its own finite bound, satisfying the complete
    new E5 table (empty at n≤1).

The SAME f and c work for ALL such stages. This does not prove
the first nontrivial n=2 E5 bit, generic richness, or later-horizon
persistence. -/
theorem RoleDiary.exists_chosen_good_oldCut_colour_with_small_generic_extensions
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hOldNonempty : (countableDiaryLeafPrefix H m).Nonempty) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
        Fin (oldStageTailCut H m f) → Bool,
        (∃ v : Nat,
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m v ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) v = c) ∧
        (∀ {n : Nat}, n ≤ 1 →
          ∀ s : FiniteGenericStage G G.graph n,
            (∀ i : Fin n,
              DiaryLowerBoundColors.singletonColour K
                (oldStageTailCut H m f)
                (F (s.image i).val) = c) →
            ∃ v : Nat,
              s.bound ≤ v ∧
              DiaryLowerBoundColors.singletonColour K
                (oldStageTailCut H m f) (F v) = c ∧
              ∀ i j : Fin n, i < j →
                (G.graph.edge i.val j.val n ↔
                  G.graph.edge (s.image i).val
                    (s.image j).val v)) := by
  classical
  obtain ⟨f, P, c, hRec, _hSaturated⟩ :=
    DH.exists_chosen_old_support_with_saturated_good_colour
      DK G F hFLeaf m hm hOldNonempty
  obtain ⟨t₀, _hHigh₀, hColour₀, hGood₀⟩ := hRec 0
  refine ⟨f, P, c, ⟨F t₀, hGood₀, hColour₀⟩, ?_⟩
  have hTargetCofinal : ∀ M : Nat,
      ∃ t : Nat,
        M < F t ∧
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (F t) = c := by
    intro M
    obtain ⟨t, ht, hColour, _hGood⟩ := hRec M
    exact ⟨t, ht, hColour⟩
  have hSourceCofinal : ∀ B : Nat,
      ∃ t : Nat, B ≤ t ∧
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (F t) = c :=
    source_index_cofinal_of_target_value_cofinal
      (fun t : Nat => F t)
      (fun t : Nat =>
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (F t) = c)
      hTargetCofinal
  intro n hn s hs
  exact small_generic_extension_of_source_index_cofinal
    G
    (fun t : Nat =>
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (F t) = c)
    hSourceCofinal hn s hs

end DiaryLeafPriority
end ThreeUniformDiaries
