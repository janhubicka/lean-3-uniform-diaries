import ThreeUniformDiaries.DiaryFiniteCanonicalCausalCrossTwoMeet
import ThreeUniformDiaries.DiaryFiniteCanonicalCrossTwoMeetCountable
import ThreeUniformDiaries.DiaryFiniteCrossCopyTwoMeetSupport
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalRankIntersections

/-!
# A genuine crossbranch S2 witness in the FINITE FULL sign-rooted diary

This combines three previously independently audited interfaces:
(1) exact crossbranch pair meet in the finite causal V/E graph;
(2) preservation of that meet by dummy-tail and one-pass completion
    at a genuine old two-split, with no same-branch restriction;
(3) exact preservation through nonconvex finite leaf-meet support,
    retaining all four original leaf images and the shared split.

The conclusion is about the actual concrete finite full target
and explicit canonical source maps, not about arbitrary copies or
Classical.choose witnesses. This is the geometric witness needed
for uniform target-flip E3 separation. The theorem does not assert
the feedback map is injective or the general absorption result.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The exact full pair meet between two different original
canonical source branches, in the FINAL finite full diary.
A causal meet at their shared 2-split survives the tail,
the one-pass insertion, and nonconvex finite reindexing. -/
theorem canonicalCausalOrbitFinite_crossTwoMeet_of_causal
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (bits : Nat → Bool)
    (PT : RolePrediary (canonicalCausalCountableCarrier DA bits))
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v w z : Nat)
    (hs : IsTwoSplit A s) (hsn : s < n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (huv : u < v) (hwz : w < z)
    (hvn : v < n) (hzn : z < n)
    (hsu : s < u) (hsw : s < w)
    (hu : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph i) u)
    (hv : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph i) v)
    (hw : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph j) w)
    (hz : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph j) z)
    (hCausal :
      (finiteCanonicalCausalMarkerGraph DA).twoMeetLevel
        (finiteCanonicalSourceRankMap DA i u)
        (finiteCanonicalSourceRankMap DA i v)
        (finiteCanonicalSourceRankMap DA j w)
        (finiteCanonicalSourceRankMap DA j z) =
      finiteCanonicalSourceRankMap DA i s) :
    (canonicalCausalOrbitFiniteTarget DA bits).twoMeetLevel
      (canonicalCausalOrbitFiniteSourceMap DA bits i u)
      (canonicalCausalOrbitFiniteSourceMap DA bits i v)
      (canonicalCausalOrbitFiniteSourceMap DA bits j w)
      (canonicalCausalOrbitFiniteSourceMap DA bits j z) =
    canonicalCausalOrbitFiniteSourceMap DA bits i s := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let C := finiteCanonicalCausalMarkerGraph DA
  let N := Fintype.card (FiniteCanonicalSignRootedVertex DA)
  let H := canonicalCausalCountableCarrier DA bits
  let G := onePassRawTarget H
  let L := canonicalCausalOrbitFiniteLeaves DA bits
  let S := canonicalCausalOrbitFiniteSupport DA bits
  let ri := finiteCanonicalSourceRankMap DA i
  let rj := finiteCanonicalSourceRankMap DA j
  have hun : u < n := by omega
  have hwn : w < n := by omega
  have hRankShared : ri s = rj s := by
    have heq : finiteCanonicalNodeAt DA i s hsn =
        finiteCanonicalNodeAt DA j s hsn := Subtype.ext hShared
    rw [finiteCanonicalSourceRankMap_of_lt DA i s hsn,
        finiteCanonicalSourceRankMap_of_lt DA j s hsn]
    exact congrArg
      (fun X : FiniteCanonicalSignRootedVertex DA =>
        (finiteCanonicalNodeIndex DA X).val) heq
  have Ei : FiniteMeetEmbedding (F.graph i) C n ri :=
    finiteCanonicalCausalMarkerGraph_sourceFiniteMeetEmbedding DA i
  have Ej : FiniteMeetEmbedding (F.graph j) C n rj :=
    finiteCanonicalCausalMarkerGraph_sourceFiniteMeetEmbedding DA j
  have hSplitSource : IsTwoSplit (F.graph i) s :=
    ((F.flip i).role_iff s hs.1 hsn).2.2.mp hs
  have hSplit : IsTwoSplit C (ri s) :=
    (Ei.twoSplit_iff s hs.1 hsn).mpr hSplitSource
  have hLeafIu : IsLeaf C (ri u) :=
    (Ei.leaf_iff u hu.1 hun).mpr hu
  have hLeafIv : IsLeaf C (ri v) :=
    (Ei.leaf_iff v hv.1 hvn).mpr hv
  have hLeafJw : IsLeaf C (rj w) :=
    (Ej.leaf_iff w hw.1 hwn).mpr hw
  have hLeafJz : IsLeaf C (rj z) :=
    (Ej.leaf_iff z hz.1 hzn).mpr hz
  have hCausalt : C.twoMeetLevel (ri u) (ri v) (rj w) (rj z) = ri s :=
    hCausal
  have hCountable :
      G.twoMeetLevel
        (canonicalCausalCountableSourceMap DA bits i u)
        (canonicalCausalCountableSourceMap DA bits i v)
        (canonicalCausalCountableSourceMap DA bits j w)
        (canonicalCausalCountableSourceMap DA bits j z) =
        canonicalCausalCountableSourceMap DA bits i s := by
    have h := finiteDummyTail_onePass_crossTwoMeet_exact
      (G := C) (N := N)
      (finiteCanonicalCausalMarkerGraph_finiteFrame DA)
      bits PT (ri s) (ri u) (ri v) (rj w) (rj z)
      hSplit
      ((finiteCanonicalSourceRankMap_strictMono DA i) huv)
      ((finiteCanonicalSourceRankMap_strictMono DA j) hwz)
      hLeafIu hLeafIv hLeafJw hLeafJz
      ((finiteCanonicalSourceRankMap_strictMono DA i) hsu)
      (by rw [hRankShared]
          exact (finiteCanonicalSourceRankMap_strictMono DA j) hsw)
      (finiteCanonicalSourceRankMap_lt_carrier DA i u hun)
      (finiteCanonicalSourceRankMap_lt_carrier DA i v hvn)
      (finiteCanonicalSourceRankMap_lt_carrier DA j w hwn)
      (finiteCanonicalSourceRankMap_lt_carrier DA j z hzn)
      hCausalt
    exact h
  have hDiary : RoleDiary G := onePassRawTarget_isDiary PT
  have PG : FiniteRolePrediaryBlock C N :=
    finiteCanonicalCausalMarkerGraph_finitePrediary DA
  have hEmb (t : FiniteCanonicalFlipIndex A n) :
      FiniteMeetEmbedding (F.graph t) G n
        (canonicalCausalCountableSourceMap DA bits t) := by
    have Et : FiniteMeetEmbedding (F.graph t) C n
        (finiteCanonicalSourceRankMap DA t) :=
      finiteCanonicalCausalMarkerGraph_sourceFiniteMeetEmbedding DA t
    have hBound : ∀ x : Nat, 3 ≤ x → x < n →
        finiteCanonicalSourceRankMap DA t x < N := by
      intro x _h xlt
      exact finiteCanonicalSourceRankMap_lt_carrier DA t x xlt
    change FiniteMeetEmbedding (F.graph t)
      (onePassRawTarget (finiteDummyTailCarrier C N bits)) n
      (fun x => onePassOldImage (finiteDummyTailCarrier C N bits)
        (finiteCanonicalSourceRankMap DA t x))
    exact Et.through_countable_completion PG
      (F.flip t).target_diary hBound bits PT
  have hSelected (t : FiniteCanonicalFlipIndex A n) :
      ∀ x : Nat, 3 ≤ x → x < n →
        IsLeaf (F.graph t) x →
        canonicalCausalCountableSourceMap DA bits t x ∈ L := by
    intro x hx hxn hxLeaf
    exact canonicalCausalOrbitFiniteLeaves_mem DA bits t
      x hx hxn hxLeaf
  have hRange (t : FiniteCanonicalFlipIndex A n) :
      ∀ x : Nat, x < n →
        canonicalCausalCountableSourceMap DA bits t x ∈ S := by
    exact (hEmb t).range_subset_leafMeetSupport
      (F.flip t).target_diary L (hSelected t)
  have hSharedCountable :
      canonicalCausalCountableSourceMap DA bits i s =
      canonicalCausalCountableSourceMap DA bits j s :=
    congrArg (onePassOldImage H) hRankShared
  change (finiteSupportGraph G S).twoMeetLevel
      (finiteSupportLift S n
        (canonicalCausalCountableSourceMap DA bits i) u)
      (finiteSupportLift S n
        (canonicalCausalCountableSourceMap DA bits i) v)
      (finiteSupportLift S n
        (canonicalCausalCountableSourceMap DA bits j) w)
      (finiteSupportLift S n
        (canonicalCausalCountableSourceMap DA bits j) z) =
    finiteSupportLift S n
      (canonicalCausalCountableSourceMap DA bits i) s
  exact finiteMeetEmbeddings_crossTwoMeet_through_support
    hDiary (hEmb i) (hEmb j) S (hRange i) (hRange j)
    s u v w z hsn hsu hsw huv hwz hvn hzn
    hSplitSource hSharedCountable hCountable

end DiaryLeafPriority
end ThreeUniformDiaries
