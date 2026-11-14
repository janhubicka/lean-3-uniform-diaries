import ThreeUniformDiaries.DiaryFixedHorizonCofinalGoodOldColour
import ThreeUniformDiaries.DiaryGoodColourSmallGenericExtensions

/-!
# Track C: fixed-horizon q-good colour also extends generic stages of size <=1

English-first adversarial audit: janhubicka/3-uniform-diaries PR #345.

For ANY fixed future finite diary source horizon q>=m+1, the
previously checked Track C theorem selects one complete genuine
reserved old support f and one full oldStageTailCut mixed colour c,
with cofinally high ACTUAL q-stage reserved witnesses compatible
with that same f and having new-leaf colour c.

Numerical target-value cofinality implies cofinality among original
generic source indices regardless of nonmonotonicity of F. It follows
that this SAME q-selected f,c satisfies the finite generic
one-point extension tests at n=0 and n=1: no old pair exists yet,
so the new E5 edge/nonedge table is empty.

The FIRST genuinely new generic E5 bit is at n=2. This result
DOES NOT assert its extension, a good induced generic subcopy,
one q-stage over every high same-colour target leaf, a persistent
next-leaf image through all future q, or countable diary
unavoidability/big Ramsey degrees.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A prescribed finite horizon q admits the SAME complete genuine
reserved old support f and full mixed singleton colour c with both:
cofinally many ACTUAL compatible q-stage witnesses in that colour,
and genuine one-point generic extensions for ALL c-coloured
finite increasing G-stages of size at most one.

No n=2 generic E5 extension is asserted. f,c may depend on q. -/
theorem RoleDiary.exists_fixed_horizon_good_oldCut_colour_with_small_generic_extensions
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m q : Nat) (hmq : m + 1 ≤ q)
    (hm : IsLeaf H m)
    (hOldNonempty : (countableDiaryLeafPrefix H m).Nonempty) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
        Fin (oldStageTailCut H m f) → Bool,
        c ∈ goodOldCutCandidateColours H K
          (fun t : Nat => F t) f m ∧
        (∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
          M < F t ∧
          ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m = F t ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c) ∧
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
  obtain ⟨f,Pf,c,hQ,hPalette,_hFull,_hSaturated⟩ :=
    DH.exists_fixed_horizon_cofinal_good_oldCut_colour
      DK G F hFLeaf m q hmq hm hOldNonempty
  have hTargetCofinal : ∀ M : Nat,
      ∃ t : Nat, M < F t ∧
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (F t) = c := by
    intro M
    obtain ⟨t,g,hHigh,_Q,_hOld,_hNew,hColour⟩ := hQ M
    exact ⟨t,hHigh,hColour⟩
  have hSourceCofinal : ∀ B : Nat, ∃ t : Nat, B ≤ t ∧
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (F t) = c :=
    source_index_cofinal_of_target_value_cofinal
      (fun t : Nat => F t)
      (fun t : Nat =>
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (F t) = c)
      hTargetCofinal
  refine ⟨f,Pf,c,hPalette,hQ,?_⟩
  intro n hn s hs
  exact small_generic_extension_of_source_index_cofinal
    G
    (fun t : Nat =>
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (F t) = c)
    hSourceCofinal hn s hs

end DiaryLeafPriority
end ThreeUniformDiaries
