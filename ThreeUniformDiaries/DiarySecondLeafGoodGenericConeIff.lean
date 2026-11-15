import ThreeUniformDiaries.DiarySecondLeafRootedGenericEligibility

/-!
# Track A: a generic cone of genuinely reserved second-leaf successors
# iff some exact favourable rooted S1 fibre contains whole generic copies

English-first adversarial proof:
  3-uniform-diaries/notes/
    track_a_good_generic_second_leaf_cone_iff_favourable_generic_split_20261115.md

Fix one GENUINE complete reserved old source support f at the SECOND
selected source diary leaf m, with unique earlier selected true leaf a.
The outer target F is an arbitrary UNORDERED induced copy of the actual
enumerated generic 3-hypergraph, consisting of TRUE target diary leaves.

The following are equivalent:
  (1) for every numerical target cutoff, the ORIGINAL F-range contains
      a WHOLE induced generic subcopy whose EVERY leaf is the image of a
      REAL old-f-compatible fully reserved immediate m+1 successor;
  (2) some ONE target rooted one-split s<f(a) satisfies the SOURCE E2
      polarity and BOTH old numerical reserve gaps, and its exact
      oneMeet(f(a),-) fibre in the ORIGINAL F range contains WHOLE
      induced generic subcopies beyond EVERY target cutoff.

The key converse first selects ONE all-good induced generic subcopy J,
then applies checked generic rooted split selection INSIDE J, and
uses the genuine fixed-v reserved-successor iff to prove favourable
polarity/gaps from an ACTUAL leaf in the selected generic split fibre.
No complete old-cut singleton-colour homogeneity is assumed.

This is an exact existence CONDITION, not an unconditional construction
of either side: high/cofinal favourable fibres (#1520/#1530) need not
contain an induced generic copy. A good immediate generic cone also
does not make any fixed next-leaf image persistent through later
SOURCE horizons. No countable diary unavoidability is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For a FIXED genuine reserved old stage at the SECOND true source
leaf, the existence of arbitrarily late WHOLE unordered induced
generic target copies consisting entirely of ACTUAL full-old-support-
compatible reserved immediate successors is equivalent to the
existence of one SOURCE-FAVOURABLE exact rooted one-split s whose
target fibre contains arbitrarily late WHOLE generic copies.

All returned copies lie literally in the ORIGINAL F[G] range; no
target-order monotonicity of F or homogeneous singleton-colour
hypothesis is required. This equivalence proves neither existential
condition unconditionally and does not address future source-horizon
persistence or the full countable diary embedding. -/
theorem RoleDiary.second_leaf_good_generic_cones_iff_favourable_generic_rooted_fibre
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (a m : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (f : Nat → Nat)
    (P : ReservedDiaryStage H K (fun t : Nat => F t) m f) :
    (∀ M : Nat,
      ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
        ∀ t : Nat,
          M < J t ∧ IsLeaf K (J t) ∧
          (∃ i : Nat, J t = F i) ∧
          HasCompatibleReservedNextLeaf H K
            (fun i : Nat => F i) f m (J t)) ↔
    (∃ s : Nat,
      IsOneSplit K s ∧ s < f a ∧
      (H.edge 0 (H.oneMeetLevel a m) m ↔
        ¬ K.edge 0 s (f a)) ∧
      H.oneMeetLevel a m ≤ s ∧
      s + (a - H.oneMeetLevel a m) ≤ f a ∧
      ∀ M : Nat,
        ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
          ∀ t : Nat,
            M < J t ∧ IsLeaf K (J t) ∧
            (∃ i : Nat, J t = F i) ∧
            K.oneMeetLevel (f a) (J t) = s) := by
  classical
  have haSelected : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  have haSupported : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a haSelected
  have hwLeaf : IsLeaf K (f a) :=
    P.1.leaf_role a haSupported ha
  constructor
  · intro hGood
    obtain ⟨J, hJGood⟩ := hGood (f a)
    have hJLeaf (t : Nat) : IsLeaf K (J t) :=
      (hJGood t).2.1
    have hJInF (t : Nat) : ∃ i : Nat, J t = F i :=
      (hJGood t).2.2.1
    obtain ⟨s, hsRole, hsBelow, hGenericJ⟩ :=
      DK.exists_one_root_split_with_generic_subcopies_all_bounds
        G J hJLeaf (f a) hwLeaf
    obtain ⟨u₀, _hu₀, hAt⟩ :=
      hGenericJ (f a + (m - a))
    have hLate : f a + (m - a) ≤ J (u₀ 0) :=
      (hAt 0).1.le
    have hMeet : K.oneMeetLevel (f a) (J (u₀ 0)) = s :=
      (hAt 0).2
    have hActualGood : HasCompatibleReservedNextLeaf H K
        (fun i : Nat => F i) f m (J (u₀ 0)) :=
      (hJGood (u₀ 0)).2.2.2
    obtain ⟨hBit, hGap1, hGap2⟩ :=
      (DH.second_leaf_late_rooted_image_reserved_iff_favourable
        DK (fun t : Nat => F t) f a m s ha hm ham hOld P
        hsRole hsBelow (J (u₀ 0)) hLate
        (hJLeaf (u₀ 0)) (hJInF (u₀ 0)) hMeet).mp hActualGood
    refine ⟨s, hsRole, hsBelow, hBit, hGap1, hGap2, ?_⟩
    intro M
    obtain ⟨u, _hu, hAll⟩ := hGenericJ M
    let U : Ordered3Graph.UnorderedEmbedding G.graph K :=
      J.comp u.asUnordered
    refine ⟨U, ?_⟩
    intro t
    obtain ⟨hHigh, hMeetT⟩ := hAll t
    exact ⟨hHigh, hJLeaf (u t), hJInF (u t), hMeetT⟩
  · rintro ⟨s, hsRole, hsBelow, hBit, hGap1, hGap2, hGeneric⟩ M
    obtain ⟨J, hAll⟩ := hGeneric (max M (f a + (m - a)))
    refine ⟨J, ?_⟩
    intro t
    obtain ⟨hHigh, hLeaf, hRange, hMeet⟩ := hAll t
    have hAboveM : M < J t :=
      lt_of_le_of_lt (le_max_left _ _) hHigh
    have hLate : f a + (m - a) ≤ J t :=
      (le_max_right M (f a + (m - a))).trans hHigh.le
    have hGood : HasCompatibleReservedNextLeaf H K
        (fun i : Nat => F i) f m (J t) :=
      DH.second_leaf_favourable_split_saturates_entire_late_fibre
        DK (fun i : Nat => F i) f a m s ha hm ham hOld P
        hsRole hsBelow hBit hGap1 hGap2
        (J t) hLate hLeaf hRange hMeet
    exact ⟨hAboveM, hLeaf, hRange, hGood⟩

end DiaryLeafPriority
end ThreeUniformDiaries
