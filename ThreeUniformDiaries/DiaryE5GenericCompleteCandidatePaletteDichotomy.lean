import ThreeUniformDiaries.DiaryFiniteGoodOldCutCandidateColours
import ThreeUniformDiaries.DiaryGenericOldStageRequiredE5Copy
import ThreeUniformDiaries.DiaryGenericCompleteOneNewS1S2

/-!
# Track C: source-correct E5 generic cones have an exact finite-candidate dichotomy

Fix an ACTUAL reserved old support f and genuine new source leaf m.
First construct an entire induced generic subcopy J of the ORIGINAL
prescribed F-range in which EVERY leaf realizes ALL source-required
old-pair E5 edge AND nonedge bits. Then apply uniform generic complete
S1 and BOTH S2 numerical profile homogenization INSIDE J, choosing the
COMPLETE mixed singleton colour at the ACTUAL old-support cut
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
  let L := countableDiaryLeafPrefix H m
  let W := L.image f
  let B := oldStageTailCut H m f
  obtain ⟨J,hRange,hE5⟩ :=
    P.exists_generic_leaf_subcopy_realizing_all_required_old_E5
      G F hFLeaf f 0
  have hJLeaves (t : Nat) : IsLeaf K (J t) :=
    (hRange t).2.1
  have hRoots (w : Nat) (hw : w ∈ W) : IsLeaf K w := by
    obtain ⟨a,ha,hfa⟩ := Finset.mem_image.mp hw
    have haSupport : a ∈ countableDiaryFiniteSupport H m :=
      mem_finiteLeafMeetSupport_leaf H L a ha
    have haLeaf : IsLeaf H a :=
      ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
    have hLeaf := P.1.leaf_role a haSupport haLeaf
    simpa only [hfa] using hLeaf
  have hWBound :
      W.sup (fun w : Nat => w) ≤ L.sup f := by
    apply Finset.sup_le
    intro w hw
    obtain ⟨a,ha,hfa⟩ := Finset.mem_image.mp hw
    simpa only [hfa] using (Finset.le_sup (f := f) ha)
  have hCut : W.sup (fun w : Nat => w) < B := by
    change W.sup (fun w : Nat => w) <
      max ((countableDiaryFiniteSupport H m).sup f) (L.sup f) + 1
    exact lt_of_le_of_lt
      (hWBound.trans (le_max_right _ _)) (Nat.lt_succ_self _)
  obtain ⟨c,_p,_q,_r,_hOne,_hCross,_hNewNew,hAll⟩ :=
    DK.exists_uniform_generic_complete_oneNew_S1_S2_profiles
      G J hJLeaves W hRoots B hCut
  refine ⟨J, ?_, c, ?_⟩
  · intro t
    obtain ⟨_hHigh,hLeaf,i,hi⟩ := hRange t
    exact ⟨hLeaf,⟨i,hi⟩,hE5 t⟩
  · intro M
    obtain ⟨u,hu,hUniform⟩ := hAll (max M B)
    refine ⟨u,hu,?_⟩
    intro t
    obtain ⟨hHigh,hLeaf,hColour,_hOne,_hCross,_hNewNew⟩ :=
      hUniform t
    have hM : M < J (u t) :=
      lt_of_le_of_lt (le_max_left _ _) hHigh
    have hB : B ≤ J (u t) :=
      (le_max_right _ _).trans hHigh.le
    have hF : ∃ i : Nat, J (u t) = F i := by
      obtain ⟨_hAbove,_hLeaf,i,hi⟩ := hRange (u t)
      exact ⟨i,hi⟩
    have hCandidateIff :=
      P.1.full_candidate_iff_good_oldCut_colour
        hm hB hLeaf hF
    refine ⟨hM,hColour,?_⟩
    simpa only [hColour] using hCandidateIff

end DiaryLeafPriority
end ThreeUniformDiaries
