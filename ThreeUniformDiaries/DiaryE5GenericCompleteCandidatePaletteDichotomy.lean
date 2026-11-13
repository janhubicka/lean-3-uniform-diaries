import ThreeUniformDiaries.DiaryFiniteGoodOldCutCandidateColours
import ThreeUniformDiaries.DiaryOldCutE5NumericReservedGenericCones

/-!
# Track C: source-correct E5 generic cones have an exact finite-candidate dichotomy

Fix an ACTUAL reserved old support f and genuine new source leaf m.
Use the independently verified exact-old-cut E5/S1/S2 reservoir theorem
to obtain an induced generic subcopy J of the ORIGINAL prescribed F-range
with ALL source-required old-pair E5 edge/nonedge bits. That theorem
already homogenizes the COMPLETE mixed singleton colour at the cut
B = oldStageTailCut H m f, not merely at the selected-old-leaf cut.

The same B-colour c occurs on arbitrarily late genuine induced generic
subcopies J∘u. The fully verified Track C finite-palette equivalence
shows, simultaneously for EVERY vertex of EVERY such subcopy:

  FullFiniteCandidate(vertex) ↔ c ∈ goodOldCutCandidateColours.

Consequently there is a sharp dichotomy: the E5-correct homogeneous
generic cones are ENTIRELY finite-admissible or ENTIRELY not. In the
negative case, all old-pair E5 tests are already correct; the remaining
failure must lie in generator functionality, numerical S1/S2, E2/E3,
strict order, roles, or another field of the complete candidate.

Neither c being good, FutureOrderReserve, genericity of an independently
chosen good colour, nor coherent later-horizon persistence follows.
No countable unavoidability or BRD theorem is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For ANY genuine reserved old source stage, select a whole
source-required-E5 induced generic leaf copy J and a complete
mixed old-support-cut colour c with arbitrarily late generic
homogeneous subcopies. On EVERY such subcopy, the ENTIRE
finite candidate predicate is EQUIVALENT to membership of c
in the finite good candidate palette.

In particular, the E5-correct generic cones have a uniform
yes/no finite-admissibility status. The selected c may be bad.
The independently selected full target S1/S2 profiles are
supplied by the imported generic profile theorem but are not
required in the conclusion of this classification. -/
theorem ReservedDiaryStage.exists_source_E5_generic_cones_with_exact_candidate_palette
    {H K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m : Nat} (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m) :
    let B := oldStageTailCut H m f
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat,
        IsLeaf K (J n) ∧
        (∃ t : Nat, J n = F t) ∧
        (∀ a b : Nat,
          a ∈ countableDiaryLeafPrefix H m →
          b ∈ countableDiaryLeafPrefix H m →
          a < b →
          (H.edge a b m ↔ K.edge (f a) (f b) (J n)))) ∧
      ∃ c : Fin B → Fin B → Bool,
        ∀ M : Nat,
          ∃ u : Ordered3Graph.Embedding G.graph G.graph,
            u.AuxTypeRespecting ∧
            ∀ n : Nat,
              M < J (u n) ∧
              DiaryLowerBoundColors.singletonColour K B (J (u n)) = c ∧
              (FiniteNewLeafCandidateCondition H K F m f (J (u n)) ↔
                c ∈ goodOldCutCandidateColours H K F f m) := by
  classical
  let B := oldStageTailCut H m f
  obtain ⟨J,hJ,c,_p,_q,_r,_hOne,_hCross,_hNewNew,hAll⟩ :=
    DK.exists_uniform_source_E5_generic_full_oldCut_S1_S2_cones
      G F hFLeaf f P
  refine ⟨J,hJ,c,?_⟩
  intro M
  obtain ⟨u,hu,hUniform⟩ := hAll (max M B)
  refine ⟨u,hu,?_⟩
  intro t
  obtain ⟨hHigh,hColour,_hE5,_hOneMeet,_hCrossMeet,_hNewMeet⟩ :=
    hUniform t
  have hLeaf : IsLeaf K (J (u t)) := (hJ (u t)).1
  have hF : ∃ i : Nat, J (u t) = F i := (hJ (u t)).2.1
  have hM : M < J (u t) :=
    lt_of_le_of_lt (le_max_left _ _) hHigh
  have hB : B ≤ J (u t) :=
    (le_max_right _ _).trans hHigh.le
  have hCandidateIff :=
    P.1.full_candidate_iff_good_oldCut_colour hm hB hLeaf hF
  refine ⟨hM,hColour,?_⟩
  calc
    FiniteNewLeafCandidateCondition H K F m f (J (u t)) ↔
        DiaryLowerBoundColors.singletonColour K B (J (u t)) ∈
          goodOldCutCandidateColours H K F f m := hCandidateIff
    _ ↔ c ∈ goodOldCutCandidateColours H K F f m := by
      rw [hColour]

end DiaryLeafPriority
end ThreeUniformDiaries
