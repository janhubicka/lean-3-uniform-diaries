import ThreeUniformDiaries.DiaryBadGenericAvoidsBareCandidatePalette
import ThreeUniformDiaries.DiaryUniformBoundedOldStageGenericAvoidance

/-!
# Track C: uniform bounded-old-support obstruction for BARE finite candidates

English-first independent proof and adversarial scope audit:
  janhubicka/3-uniform-diaries PR #336 (finite-family addendum).

The merged Track D generic E5 avoidance construction produces one
whole induced UNORDERED generic target copy realizing the OPPOSITE
source old-pair E5 bit over EVERY actual target-ordered F-pair below
a prescribed bound B. The new Track C bare-candidate E5 necessity
lemma upgrades reserved-stage avoidance: EVERY such J leaf fails
the COMPLETE BARE finite candidate, uniformly for ALL genuine old
reserved stages f with f(b)<B.

Given a supplied finite list of genuine old stages, choose B above
all selected old b-images and one numerical cutoff above ALL their
oldStageTailCuts. The same induced J avoids the bare candidates AND
the finite candidate good-colour palettes of ALL listed stages.
This does not refute source/range JOINT selection or hitting
restricted to AuxTypeRespecting generic source embeddings.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One induced generic true-leaf copy J in the ORIGINAL F-range,
chosen only from (m,a,b,B,M), excludes BARE full finite candidates
for ALL genuine old reserved support maps f with f(b)<B.

No FutureOrderReserve is assumed, and the J-copy is NOT asserted to
be AuxTypeRespecting. -/
theorem exists_generic_subcopy_avoiding_all_bounded_bare_candidates
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (B M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat,
        M < J n ∧ B < J n ∧
        IsLeaf K (J n) ∧
        (∃ t : Nat, J n = F t)) ∧
      (∀ f : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) m f →
        f b < B →
        ∀ n : Nat,
          ¬ FiniteNewLeafCandidateCondition
            H K (fun t : Nat => F t) m f (J n)) := by
  classical
  let chi : Nat → Nat → Bool :=
    fun _ _ => decide (¬ H.edge a b m)
  obtain ⟨J, hRange, hPattern⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_target_bounded_E5_pattern
      G K F hFLeaf B M chi
  refine ⟨J, hRange, ?_⟩
  intro f P hBound n C
  have haS : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a ha
  have hbS : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) b hb
  have hOrder : f a < f b := P.1.ordered a b haS hbS hab
  have haLeaf : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  have hbLeaf : IsLeaf H b :=
    ((mem_countableDiaryLeafPrefix_iff H m b).mp hb).2.2
  obtain ⟨i, hi⟩ := P.1.leaf_range a haS haLeaf
  obtain ⟨j, hj⟩ := P.1.leaf_range b hbS hbLeaf
  have hTargetOrder : F i < F j := by
    simpa only [← hi, ← hj] using hOrder
  have hTargetBound : F j < B := by
    simpa only [← hj] using hBound
  have hOpp :
      K.edge (f a) (f b) (J n) ↔ ¬ H.edge a b m := by
    have hMask := hPattern n i j hTargetOrder hTargetBound
    simpa only [← hi, ← hj, chi, decide_eq_true_eq] using hMask
  have hCandidateBit :=
    P.bare_candidate_preserves_old_pair_E5 hm ha hb hab C
  have hImpossible : H.edge a b m ↔ ¬ H.edge a b m :=
    hCandidateBit.trans hOpp
  tauto

/-- NO finite list of genuine old reserved stages at the fixed new
source leaf can hit ALL unordered induced generic refinements,
even by their BARE complete finite candidates. One whole generic
copy avoids their finite good old-cut palettes simultaneously;
each palette is tested at that stage's OWN numerical old cut.

This theorem imposes no uniform bound on arbitrary unlisted old
stages and makes no claim about AuxTypeRespecting refinements. -/
theorem exists_generic_subcopy_avoiding_finite_stage_family_bare_palettes
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (k : Nat)
    (stages : Fin k → Nat → Nat)
    (hStages : ∀ i : Fin k, ReservedDiaryStage
      H K (fun t : Nat => F t) m (stages i))
    (M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      ∀ n : Nat,
        M < J n ∧ IsLeaf K (J n) ∧
        (∃ t : Nat, J n = F t) ∧
        (∀ i : Fin k,
          ¬ FiniteNewLeafCandidateCondition
            H K (fun t : Nat => F t) m (stages i) (J n) ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m (stages i)) (J n) ∉
            goodOldCutCandidateColours H K (fun t : Nat => F t)
              (stages i) m) := by
  classical
  let B : Nat :=
    (Finset.univ : Finset (Fin k)).sup (fun i => stages i b) + 1
  let Cut : Nat :=
    (Finset.univ : Finset (Fin k)).sup
      (fun i => oldStageTailCut H m (stages i))
  have hBound (i : Fin k) : stages i b < B := by
    have hSup :=
      Finset.le_sup (f := fun i : Fin k => stages i b)
        (Finset.mem_univ i)
    exact lt_of_le_of_lt hSup (Nat.lt_succ_self _)
  have hCut (i : Fin k) :
      oldStageTailCut H m (stages i) ≤ Cut :=
    Finset.le_sup
      (f := fun j : Fin k => oldStageTailCut H m (stages j))
      (Finset.mem_univ i)
  obtain ⟨J, hRange, hBad⟩ :=
    exists_generic_subcopy_avoiding_all_bounded_bare_candidates
      G F hFLeaf hm ha hb hab B (max M Cut)
  refine ⟨J, ?_⟩
  intro n
  obtain ⟨hLarge, _hB, hLeaf, t, hF⟩ := hRange n
  have hM : M < J n :=
    lt_of_le_of_lt (le_max_left M Cut) hLarge
  refine ⟨hM, hLeaf, ⟨t, hF⟩, ?_⟩
  intro i
  have hNoCandidate :
      ¬ FiniteNewLeafCandidateCondition
        H K F m (stages i) (J n) :=
    hBad (stages i) (hStages i) (hBound i) n
  have hAtCut : oldStageTailCut H m (stages i) ≤ J n :=
    (hCut i).trans
      ((le_max_right M Cut).trans hLarge.le)
  refine ⟨hNoCandidate, ?_⟩
  intro hInPalette
  exact hNoCandidate
    (((hStages i).1.full_candidate_iff_good_oldCut_colour
      hm hAtCut hLeaf ⟨t, hF⟩).mpr hInPalette)

end DiaryLeafPriority
end ThreeUniformDiaries
