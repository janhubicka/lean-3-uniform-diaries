import ThreeUniformDiaries.DiarySecondLeafWholeFavourableFibreTail
import ThreeUniformDiaries.DiaryRootedGenericLeafSplitCone

/-!
# Track A: exact second-leaf rooted generic eligibility, without complete old-cut colour

For the SECOND true source diary leaf m with exactly one earlier
selected source leaf a, the previously checked fixed-v reserved
successor iff and full late favourable-fibre saturation give a
POINTWISE iff: every genuine target leaf v in the ORIGINAL F range,
above the exact future gap and with oneMeet(f(a),v)=s, is a literal
old-support-compatible reserved successor image precisely when s
passes the source E2 sign and two old numerical gap tests.

Separately the checked ATR singleton-colour theorem gives, for ANY
fixed true old root f(a), one exact target S1 split s whose fibre
contains whole unordered induced generic subcopies of F[G] beyond
ALL target bounds. Combining these establishes an exact generic
ALL-GOOD / ALL-BAD fibre dichotomy without requiring a complete
oldStageTailCut singleton colour to be constant.

CRITICAL: the generically rich s is selected EXISTENTIALLY and
may FAIL the source-required favourable sign/gap tests. The prior
unconditional high favourable-root theorem chooses a DIFFERENT
existential split, cofinal but not known generic-rich. These two
split selections cannot be identified without a NEW argument.
Nothing here gives persistence of a fixed new leaf image at
later SOURCE horizons or countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For a genuine old stage at the SECOND source leaf and a fixed
genuine rooted target split s<f(a), exact future-gap and exact
meet hypotheses reduce the existence of a REAL old-compatible
reserved immediate successor image v to precisely THREE finite
conditions: source E2 sign and two old spacing inequalities.

This is a genuine pointwise IFF, not a fixed-colour approximation:
both directions use full reserved stages, target leaves in the
ORIGINAL prescribed range, and literal agreement on ALL of S_m.
No F monotonicity, genericity, or cofinal split fibre is assumed. -/
theorem RoleDiary.second_leaf_late_rooted_image_reserved_iff_favourable
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F f : Nat → Nat) (a m s : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (P : ReservedDiaryStage H K F m f)
    (hsRole : IsOneSplit K s) (hsBelow : s < f a)
    (v : Nat) (hLate : f a + (m - a) ≤ v)
    (hvLeaf : IsLeaf K v)
    (hvRange : ∃ t : Nat, v = F t)
    (hMeet : K.oneMeetLevel (f a) v = s) :
    HasCompatibleReservedNextLeaf H K F f m v ↔
      ((H.edge 0 (H.oneMeetLevel a m) m ↔
          ¬ K.edge 0 s (f a)) ∧
        H.oneMeetLevel a m ≤ s ∧
        s + (a - H.oneMeetLevel a m) ≤ f a) := by
  have haSelected : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  have haSupported : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a haSelected
  have hwLeaf : IsLeaf K (f a) :=
    P.1.leaf_role a haSupported ha
  have hwLtV : f a < v := by
    have hmPos : 0 < m - a := Nat.sub_pos_of_lt ham
    omega
  have hsLtV : s < v := lt_trans hsBelow hwLtV
  have hOpp :
      ¬ (K.edge 0 s (f a) ↔ K.edge 0 s v) :=
    DK.oneSplit_witness_opposite_marker s (f a) v
      hsRole hwLeaf hvLeaf hsBelow hsLtV hMeet
  have hTargetBit :
      K.edge 0 s v ↔ ¬ K.edge 0 s (f a) := by
    tauto
  constructor
  · rintro ⟨g,Q,hKeep,hNew⟩
    have hSelected : ∀ u : Nat,
        u ∈ countableDiaryLeafPrefix H m → g u = f u := by
      intro u hu
      exact hKeep u
        (mem_finiteLeafMeetSupport_leaf H
          (countableDiaryLeafPrefix H m) u hu)
    obtain ⟨hRight,hGap1,hGap2,_hGap3⟩ :=
      (DH.second_leaf_fixed_v_reserved_successor_iff
        DK F f a m v ha hm ham hOld P hvLeaf hvRange).mp
          ⟨g,Q,hSelected,hNew⟩
    rw [hMeet] at hRight hGap1 hGap2
    exact ⟨hRight.trans hTargetBit,hGap1,hGap2⟩
  · rintro ⟨hBit,hGap1,hGap2⟩
    exact DH.second_leaf_favourable_split_saturates_entire_late_fibre
      DK F f a m s ha hm ham hOld P
      hsRole hsBelow hBit hGap1 hGap2
      v hLate hvLeaf hvRange hMeet

/-- In EVERY original unordered induced generic true-leaf range,
with ANY fixed genuine reserved OLD support f at the SECOND source
leaf, there exists ONE genuine target S1 split s<f(a) supporting
WHOLE induced generic subcopies beyond ALL numerical bounds.

At sufficiently late points of EVERY chosen generic subcopy,
compatibility as a GENUINE reserved immediate next-leaf image
over the FIXED full old support f is equivalent, vertex-by-vertex,
to EXACTLY the SAME three finite source E2/S1 gap tests on s.

Consequently the entire generic subcopy is ALL GOOD when s passes
the tests, and ENTIRELY BAD otherwise. The existential generic
split is not asserted favourable. This does not produce a
finitely persistent next-stage image or countable unavoidability. -/
theorem RoleDiary.exists_second_leaf_generic_rooted_all_good_or_all_bad_cones
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
    ∃ s : Nat,
      IsOneSplit K s ∧ s < f a ∧
      (∀ M : Nat,
        ∃ u : Ordered3Graph.Embedding G.graph G.graph,
          u.AuxTypeRespecting ∧
          ∀ t : Nat,
            M < F (u t) ∧
            K.oneMeetLevel (f a) (F (u t)) = s ∧
            (HasCompatibleReservedNextLeaf H K
                (fun i : Nat => F i) f m (F (u t)) ↔
              ((H.edge 0 (H.oneMeetLevel a m) m ↔
                  ¬ K.edge 0 s (f a)) ∧
                H.oneMeetLevel a m ≤ s ∧
                s + (a - H.oneMeetLevel a m) ≤ f a))) := by
  classical
  have haSelected : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  have haSupported : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a haSelected
  have hwLeaf : IsLeaf K (f a) :=
    P.1.leaf_role a haSupported ha
  obtain ⟨s,hsRole,hsBelow,hGeneric⟩ :=
    DK.exists_one_root_split_with_generic_subcopies_all_bounds
      G F hFLeaf (f a) hwLeaf
  refine ⟨s,hsRole,hsBelow,?_⟩
  intro M
  obtain ⟨u,hu,hAll⟩ :=
    hGeneric (max M (f a + (m - a)))
  refine ⟨u,hu,?_⟩
  intro t
  obtain ⟨hHigh,hMeet⟩ := hAll t
  have hAbove : M < F (u t) := by
    omega
  have hLate : f a + (m - a) ≤ F (u t) := by
    omega
  have hIff :=
    DH.second_leaf_late_rooted_image_reserved_iff_favourable
      DK (fun i : Nat => F i) f a m s ha hm ham hOld
      P hsRole hsBelow (F (u t)) hLate
      (hFLeaf (u t)) ⟨u t,rfl⟩ hMeet
  exact ⟨hAbove,hMeet,hIff⟩

end DiaryLeafPriority
end ThreeUniformDiaries
