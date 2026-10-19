import ThreeUniformDiaries.DiaryFiniteBlockProtectedS2

/-!
# Transport protected finite diary pictures through meet-preserving maps

A finite diary embedding in this programme means more than an
induced relational copy: its marker roles and ALL capped numerical
singleton/full pair meets must be preserved. This is essential
for the relative one-pass completion step.

We isolate exactly the reusable *finite* interface: an increasing
map fixing Devlin markers 1,2, reflecting the genuine three roles
on nonmarker vertices, and preserving all singleton/full pair
meets in the source finite frame. The marker 0 is irrelevant
to this protected-picture lemma, but is fixed by the concrete
ordered-sum embeddings.

Every finite RoleDiary block mapped by such an interface yields
a genuine FiniteProtectedMeetPicture on its IMAGE of the nonmarker
source interval. This uses the exact finite S2 cap theorem, not
the unverified universal old-cut preservation clause.

No global diary, existence of an embedding, countable completion,
or flip absorption is postulated by the interface itself.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Precise finite numerical/role interface for a protected copy.
This is a PROP about a concrete supplied map f; it does NOT assert
that f exists. The source interval is [0,n), and meets are required
only on its genuine nonmarker vertices. -/
structure FiniteMeetEmbedding
    (H T : Ordered3Graph Nat) (n : Nat) (f : Nat → Nat) : Prop where
  strictMono : StrictMono f
  marker_one : f 1 = 1
  marker_two : f 2 = 2
  leaf_iff :
    ∀ u, 3 ≤ u → u < n → (IsLeaf T (f u) ↔ IsLeaf H u)
  oneSplit_iff :
    ∀ u, 3 ≤ u → u < n → (IsOneSplit T (f u) ↔ IsOneSplit H u)
  twoSplit_iff :
    ∀ u, 3 ≤ u → u < n → (IsTwoSplit T (f u) ↔ IsTwoSplit H u)
  oneMeet :
    ∀ u v, 3 ≤ u → u < n → 3 ≤ v → v < n →
      T.oneMeetLevel (f u) (f v) = f (H.oneMeetLevel u v)
  twoMeet :
    ∀ a b c d, a < b → c < d →
      3 ≤ a → a < n → 3 ≤ b → b < n →
      3 ≤ c → c < n → 3 ≤ d → d < n →
      T.twoMeetLevel (f a) (f b) (f c) (f d) =
        f (H.twoMeetLevel a b c d)

variable {H T : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}

/-- The complete nonmarker source interval, transported through
a concrete finite embedding; it remains a finite set in the
target regardless of the size of the ambient target. -/
def finiteMeetImage (n : Nat) (f : Nat → Nat) : Finset Nat :=
  (Finset.Ico 3 n).image f

/-- Every bounded finite diary is a protected S1/S2 picture in
the target under an exact finite meet embedding. In particular
this transfers split/leaf mixed comparisons and the correct
common-first-leaf S2 cap. -/
theorem FiniteMeetEmbedding.protected_picture
    (D : FiniteRoleDiaryBlock H n)
    (E : FiniteMeetEmbedding H T n f) :
    FiniteProtectedMeetPicture T (finiteMeetImage n f) := by
  classical
  let F := Finset.Ico 3 n
  have hSource : FiniteProtectedMeetPicture H F :=
    finiteRoleDiary_protected_picture D F (by
      intro u hu
      exact Finset.mem_Ico.mp hu)
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_image.mp hu with ⟨x,hx,rfl⟩
    have hx3 : 3 ≤ x := (Finset.mem_Ico.mp hx).1
    have h23 : 2 < x := by omega
    have hGreater := E.strictMono h23
    rw [E.marker_two] at hGreater
    omega
  · intro u v hu hv hLeafU hLeafV hne
    rcases Finset.mem_image.mp hu with ⟨a,ha,rfl⟩
    rcases Finset.mem_image.mp hv with ⟨c,hc,rfl⟩
    have ha3 : 3 ≤ a := (Finset.mem_Ico.mp ha).1
    have han : a < n := (Finset.mem_Ico.mp ha).2
    have hc3 : 3 ≤ c := (Finset.mem_Ico.mp hc).1
    have hcn : c < n := (Finset.mem_Ico.mp hc).2
    have hHa : IsLeaf H a := (E.leaf_iff a ha3 han).mp hLeafU
    have hHc : IsLeaf H c := (E.leaf_iff c hc3 hcn).mp hLeafV
    have hneSource : a ≠ c := by
      intro hac
      subst c
      exact hne rfl
    have hS1 := finiteRoleDiary_s1_unordered
      D a c han hcn hHa hHc hneSource
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
    have hS2 := finiteRoleDiary_pair_meets_exact
      D a0 b0 c0 d0 hab0 hcd0 hbn hdn hHa hHb hHc hHd
    have hPairMeet := E.twoMeet a0 b0 c0 d0
      hab0 hcd0 ha3 han hb3 hbn hc3 hcn hd3 hdn
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

end DiaryLeafPriority
end ThreeUniformDiaries
