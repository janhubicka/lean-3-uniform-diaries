import ThreeUniformDiaries.DiaryFiniteCanonicalSourceRankMap
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalOriginalSOne
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalSourceLeafMeets
import ThreeUniformDiaries.DiaryFiniteProtectedMeetPicture

/-!
# Each original canonical flip is a protected finite S1/S2 picture

The causally completed sign-rooted graph is a genuine finite V/E
pre-diary, but need not satisfy S1/S2 between arbitrary new leaves.

Here we protect ALL original nonmarker vertices on EACH canonical
source-flip branch. The source-to-target map is the actual finite
level-first rank, extended to a strictly increasing total Nat map.

Every original leaf pair has a genuine target 1-split as its
singleton meet (restricted source S1). More importantly, the
COMPLETE full leaf-pair meet between any two ordered source pairs
is preserved at the exact numerical rank, including the marker-one,
proper 2-split, and common-first-leaf capped alternatives (restricted
source S2).

Thus the image of the entire original nonmarker source interval
is a FiniteProtectedMeetPicture in the ambient finite causal
pre-diary. This is the exact input for the already verified
dummy-tail/relative one-pass protected completion machinery.

No global S1/S2 of the causal pre-diary, no source mixed-meet
embedding, and no every-target-flip absorption is asserted here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The completed graph's leaf/1-split/2-split roles agree with
the original source diary under its ACTUAL total rank map, for
all bounded source nonmarker vertices. -/
theorem finiteCanonicalSourceRankMap_roles_iff
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Nat) (hz3 : 3 ≤ z) (hzn : z < n) :
    (IsLeaf (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalSourceRankMap DA i z) ↔ IsLeaf A z) ∧
    (IsOneSplit (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalSourceRankMap DA i z) ↔ IsOneSplit A z) ∧
    (IsTwoSplit (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalSourceRankMap DA i z) ↔ IsTwoSplit A z) := by
  simpa only [finiteCanonicalSourceRankMap_of_lt DA i z hzn] using
    (finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i z hz3 hzn)

/-- The complete original nonmarker source interval, mapped
into its exact finite numerical ranks, is an ambient protected
S1/S2 picture in the ACTUAL causal sign-rooted pre-diary.

The picture includes source split vertices as well as source leaves.
Only source LEAF meet comparisons are required by its abstract
protected-picture structure. -/
theorem finiteCanonicalCausalMarkerGraph_original_protected_picture
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n) :
    FiniteProtectedMeetPicture
      (finiteCanonicalCausalMarkerGraph DA)
      (finiteMeetImage n (finiteCanonicalSourceRankMap DA i)) := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let H := F.graph i
  let G := finiteCanonicalCausalMarkerGraph DA
  let f := finiteCanonicalSourceRankMap DA i
  have hMono : StrictMono f :=
    finiteCanonicalSourceRankMap_strictMono DA i
  have hMarkerOne : f 1 = 1 :=
    finiteCanonicalSourceRankMap_marker DA i 1 (by omega)
  have hMarkerTwo : f 2 = 2 :=
    finiteCanonicalSourceRankMap_marker DA i 2 (by omega)
  have hSource : FiniteProtectedMeetPicture H (Finset.Ico 3 n) :=
    finiteRoleDiary_protected_picture
      (F.flip i).target_diary (Finset.Ico 3 n)
      (by intro z hz; exact Finset.mem_Ico.mp hz)
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨x,hx,rfl⟩
    have hx3 : 3 ≤ x := (Finset.mem_Ico.mp hx).1
    have h2x : 2 < x := by omega
    have hGreater := hMono h2x
    rw [hMarkerTwo] at hGreater
    change 3 ≤ f x
    omega
  · intro u v hu hv hLeafU hLeafV hne
    rcases Finset.mem_image.mp hu with ⟨a,ha,rfl⟩
    rcases Finset.mem_image.mp hv with ⟨c,hc,rfl⟩
    have ha3 : 3 ≤ a := (Finset.mem_Ico.mp ha).1
    have han : a < n := (Finset.mem_Ico.mp ha).2
    have hc3 : 3 ≤ c := (Finset.mem_Ico.mp hc).1
    have hcn : c < n := (Finset.mem_Ico.mp hc).2
    have hLeafA : IsLeaf A a :=
      (finiteCanonicalSourceRankMap_roles_iff
        DA i a ha3 han).1.mp hLeafU
    have hLeafC : IsLeaf A c :=
      (finiteCanonicalSourceRankMap_roles_iff
        DA i c hc3 hcn).1.mp hLeafV
    have hACne : a ≠ c := by
      intro hAC
      subst c
      exact hne rfl
    have hTarget :=
      finiteCanonicalCausalMarkerGraph_original_distinctLeaf_S1
        DA i a c han hcn hLeafA hLeafC hACne
    simpa only [
      finiteCanonicalSourceRankMap_of_lt DA i a han,
      finiteCanonicalSourceRankMap_of_lt DA i c hcn] using hTarget
  · intro a b c d ha hb hc hd hab hcd
        hLeafA hLeafB hLeafC hLeafD
    rcases Finset.mem_image.mp ha with ⟨a0,ha0,rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b0,hb0,rfl⟩
    rcases Finset.mem_image.mp hc with ⟨c0,hc0,rfl⟩
    rcases Finset.mem_image.mp hd with ⟨d0,hd0,rfl⟩
    have ha3 : 3 ≤ a0 := (Finset.mem_Ico.mp ha0).1
    have han : a0 < n := (Finset.mem_Ico.mp ha0).2
    have hb3 : 3 ≤ b0 := (Finset.mem_Ico.mp hb0).1
    have hbn : b0 < n := (Finset.mem_Ico.mp hb0).2
    have hc3 : 3 ≤ c0 := (Finset.mem_Ico.mp hc0).1
    have hcn : c0 < n := (Finset.mem_Ico.mp hc0).2
    have hd3 : 3 ≤ d0 := (Finset.mem_Ico.mp hd0).1
    have hdn : d0 < n := (Finset.mem_Ico.mp hd0).2
    have hab0 : a0 < b0 := by
      by_contra hnot
      have hba : b0 ≤ a0 := by omega
      have hMon := hMono.monotone hba
      exact (not_lt_of_ge hMon) hab
    have hcd0 : c0 < d0 := by
      by_contra hnot
      have hdc : d0 ≤ c0 := by omega
      have hMon := hMono.monotone hdc
      exact (not_lt_of_ge hMon) hcd
    have hHa : IsLeaf A a0 :=
      (finiteCanonicalSourceRankMap_roles_iff
        DA i a0 ha3 han).1.mp hLeafA
    have hHb : IsLeaf A b0 :=
      (finiteCanonicalSourceRankMap_roles_iff
        DA i b0 hb3 hbn).1.mp hLeafB
    have hHc : IsLeaf A c0 :=
      (finiteCanonicalSourceRankMap_roles_iff
        DA i c0 hc3 hcn).1.mp hLeafC
    have hHd : IsLeaf A d0 :=
      (finiteCanonicalSourceRankMap_roles_iff
        DA i d0 hd3 hdn).1.mp hLeafD
    have hFa : IsLeaf H a0 :=
      ((F.flip i).role_iff a0 hHa.1 han).1.mp hHa
    have hFb : IsLeaf H b0 :=
      ((F.flip i).role_iff b0 hHb.1 hbn).1.mp hHb
    have hFc : IsLeaf H c0 :=
      ((F.flip i).role_iff c0 hHc.1 hcn).1.mp hHc
    have hFd : IsLeaf H d0 :=
      ((F.flip i).role_iff d0 hHd.1 hdn).1.mp hHd
    have hS2 := hSource.leaf_pair_meets
      a0 b0 c0 d0 ha0 hb0 hc0 hd0
      hab0 hcd0 hFa hFb hFc hFd
    let m := H.twoMeetLevel a0 b0 c0 d0
    have hmBound : m < n := by
      have h := H.twoMeetLevel_le_min a0 b0 c0 d0
      dsimp [m]
      omega
    have hPairExact :
        G.twoMeetLevel
          (f a0) (f b0) (f c0) (f d0) = f m := by
      change G.twoMeetLevel
        (finiteCanonicalSourceRankMap DA i a0)
        (finiteCanonicalSourceRankMap DA i b0)
        (finiteCanonicalSourceRankMap DA i c0)
        (finiteCanonicalSourceRankMap DA i d0) =
          finiteCanonicalSourceRankMap DA i m
      rw [finiteCanonicalSourceRankMap_of_lt DA i a0 han,
        finiteCanonicalSourceRankMap_of_lt DA i b0 hbn,
        finiteCanonicalSourceRankMap_of_lt DA i c0 hcn,
        finiteCanonicalSourceRankMap_of_lt DA i d0 hdn,
        finiteCanonicalSourceRankMap_of_lt DA i m hmBound]
      exact finiteCanonicalCausalMarkerGraph_original_leaf_twoMeets_exact
        DA i a0 b0 c0 d0 hab0 hcd0 hbn hdn hHa hHb hHc hHd
    rcases hS2 with hMarker | hSplit | ⟨hSame,hCap⟩
    · exact Or.inl
        (hPairExact.trans ((congrArg f hMarker).trans hMarkerOne))
    · have hSplitSource : IsTwoSplit A m :=
        ((F.flip i).role_iff m hSplit.1 hmBound).2.2.mpr hSplit
      have hSplitTarget : IsTwoSplit G (f m) :=
        (finiteCanonicalSourceRankMap_roles_iff
          DA i m hSplitSource.1 hmBound).2.2.mpr hSplitSource
      exact Or.inr (Or.inl (by rw [hPairExact]; exact hSplitTarget))
    · exact Or.inr (Or.inr
        ⟨congrArg f hSame,
          hPairExact.trans (congrArg f hCap)⟩)

end DiaryLeafPriority
end ThreeUniformDiaries
