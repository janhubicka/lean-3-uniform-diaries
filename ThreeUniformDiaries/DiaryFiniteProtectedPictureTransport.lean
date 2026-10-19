import ThreeUniformDiaries.DiaryFiniteSumMeetEmbeddings

/-!
# Transport protected finite S1/S2 pictures through induced meet embeddings

A genuinely protected finite subpicture of a V/E pre-diary is
characterised by exact numerical one- and two-meet conditions
on its nonmarker vertices. An induced finite meet embedding
preserves and reflects all genuine marker roles and both meets.
These hypotheses alone transport a protected picture to the image
without assuming the entire source is already a diary.

This lemma is the compositional step needed when iterating the
finite ordered-sum construction: previously protected families
remain protected under each new left-block inclusion. The new
right diary is protected by FiniteMeetEmbedding.protected_picture.

No global countable pre-diary or every-flip absorption is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H T K : Ordered3Graph Nat}
variable {n m : Nat} {f : Nat → Nat} {F : Finset Nat}

/-- Arbitrary finite S1/S2 protected pictures transport under any
actual induced finite meet embedding whose source domain includes
the whole picture. The source need only be a V/E pre-diary. -/
theorem FiniteMeetEmbedding.transport_protected_picture
    (E : FiniteMeetEmbedding H T n f)
    (Q : FiniteProtectedMeetPicture H F)
    (hF : ∀ u : Nat, u ∈ F → u < n) :
    FiniteProtectedMeetPicture T (F.image f) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_image.mp hu with ⟨x,hx,rfl⟩
    have hx3 : 3 ≤ x := Q.above_markers x hx
    have h23 : 2 < x := by omega
    have hGreater := E.strictMono h23
    rw [E.marker_two] at hGreater
    omega
  · intro u v hu hv hLeafU hLeafV hne
    rcases Finset.mem_image.mp hu with ⟨a,ha,rfl⟩
    rcases Finset.mem_image.mp hv with ⟨c,hc,rfl⟩
    have ha3 : 3 ≤ a := Q.above_markers a ha
    have hc3 : 3 ≤ c := Q.above_markers c hc
    have han : a < n := hF a ha
    have hcn : c < n := hF c hc
    have hHa : IsLeaf H a :=
      (E.leaf_iff a ha3 han).mp hLeafU
    have hHc : IsLeaf H c :=
      (E.leaf_iff c hc3 hcn).mp hLeafV
    have hneSource : a ≠ c := by
      intro hac
      subst c
      exact hne rfl
    have hS1 := Q.singleton_split a c ha hc hHa hHc hneSource
    have hMeetBound : H.oneMeetLevel a c < n := by
      have hLe := H.oneMeetLevel_le_min a c
      omega
    have hS3 : 3 ≤ H.oneMeetLevel a c := hS1.1
    have hSplitT : IsOneSplit T (f (H.oneMeetLevel a c)) :=
      (E.oneSplit_iff (H.oneMeetLevel a c) hS3 hMeetBound).mpr hS1
    rw [E.oneMeet a c ha3 han hc3 hcn]
    exact hSplitT
  · intro a b c d ha hb hc hd hab hcd hLeafA hLeafB hLeafC hLeafD
    rcases Finset.mem_image.mp ha with ⟨a0,ha0,rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b0,hb0,rfl⟩
    rcases Finset.mem_image.mp hc with ⟨c0,hc0,rfl⟩
    rcases Finset.mem_image.mp hd with ⟨d0,hd0,rfl⟩
    have ha3 : 3 ≤ a0 := Q.above_markers a0 ha0
    have hb3 : 3 ≤ b0 := Q.above_markers b0 hb0
    have hc3 : 3 ≤ c0 := Q.above_markers c0 hc0
    have hd3 : 3 ≤ d0 := Q.above_markers d0 hd0
    have han : a0 < n := hF a0 ha0
    have hbn : b0 < n := hF b0 hb0
    have hcn : c0 < n := hF c0 hc0
    have hdn : d0 < n := hF d0 hd0
    have hab0 : a0 < b0 := by
      by_contra hnot
      have hba : b0 ≤ a0 := by omega
      have hMon := E.strictMono.monotone hba
      omega
    have hcd0 : c0 < d0 := by
      by_contra hnot
      have hdc : d0 ≤ c0 := by omega
      have hMon := E.strictMono.monotone hdc
      omega
    have hHa : IsLeaf H a0 := (E.leaf_iff a0 ha3 han).mp hLeafA
    have hHb : IsLeaf H b0 := (E.leaf_iff b0 hb3 hbn).mp hLeafB
    have hHc : IsLeaf H c0 := (E.leaf_iff c0 hc3 hcn).mp hLeafC
    have hHd : IsLeaf H d0 := (E.leaf_iff d0 hd3 hdn).mp hLeafD
    have hS2 := Q.leaf_pair_meets a0 b0 c0 d0
      ha0 hb0 hc0 hd0 hab0 hcd0 hHa hHb hHc hHd
    have hPairMeet := E.twoMeet a0 b0 c0 d0 hab0 hcd0
      ha3 han hb3 hbn hc3 hcn hd3 hdn
    rcases hS2 with hMarker | hSplit | ⟨hSame,hCap⟩
    · exact Or.inl
        (hPairMeet.trans ((congrArg f hMarker).trans E.marker_one))
    · have hMeetBound : H.twoMeetLevel a0 b0 c0 d0 < n := by
        have hLe := H.twoMeetLevel_le_min a0 b0 c0 d0
        omega
      have hMeet3 : 3 ≤ H.twoMeetLevel a0 b0 c0 d0 := hSplit.1
      have hSplitT : IsTwoSplit T (f (H.twoMeetLevel a0 b0 c0 d0)) :=
        (E.twoSplit_iff (H.twoMeetLevel a0 b0 c0 d0)
          hMeet3 hMeetBound).mpr hSplit
      exact Or.inr (Or.inl (by rw [hPairMeet]; exact hSplitT))
    · exact Or.inr (Or.inr
        ⟨congrArg f hSame, hPairMeet.trans (congrArg f hCap)⟩)

/-- Adjoining a genuine finite diary to a finite V/E pre-diary
simultaneously preserves ANY existing finite protected picture
in the left block, and produces a new protected right diary copy.
Both are embedded into the SAME verified finite V/E pre-diary. -/
theorem exists_finiteTwoBlock_preserves_left_picture
    (PH : FiniteRolePrediaryBlock H n)
    (DK : FiniteRoleDiaryBlock K m)
    (Q : FiniteProtectedMeetPicture H F)
    (hF : ∀ u : Nat, u ∈ F → u < n) :
    ∃ bits : Nat → Bool,
      FiniteRolePrediaryBlock
        (finiteTwoBlockCarrier H K n m bits)
        (finiteTwoBlockLength n m) ∧
      FiniteProtectedMeetPicture
        (finiteTwoBlockCarrier H K n m bits) F ∧
      FiniteProtectedMeetPicture
        (finiteTwoBlockCarrier H K n m bits)
        (finiteMeetImage m (rightBlockImage n)) := by
  obtain ⟨bits, PG, ELeft, ERight⟩ :=
    exists_finiteTwoBlock_both_meetEmbeddings PH DK
  refine ⟨bits, PG, ?_, ERight.protected_picture DK⟩
  have QL : FiniteProtectedMeetPicture
      (finiteTwoBlockCarrier H K n m bits)
      (F.image (fun x : Nat => x)) :=
    ELeft.transport_protected_picture Q hF
  simpa using QL

end DiaryLeafPriority
end ThreeUniformDiaries
