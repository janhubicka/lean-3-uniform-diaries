import ThreeUniformDiaries.DiaryRelativeFiniteFamilyPrefixCompression
import ThreeUniformDiaries.DiaryAmbientBoundedCopyExactPrefixCompression
import Lean.Elab.Tactic.Omega

/-!
# Track B: finite-family compression with one chosen old copy fixed exactly

The already verified finite-family compression theorem preserves an
ambient numerical prefix and gives *some* induced all-meet embedding
for every input diary. The independently verified exact-old-image
compression theorem keeps one specified given map literally unchanged
but does not simultaneously accommodate further finite diary copies.

Here we combine both interfaces, by generating ONE ambient finite
leaf-meet support from:
* all leaf images of the specified old finite copy f:A->G;
* all leaf images of finitely many other already supplied diary
  copies into the SAME countable full RoleDiary G;
* finite leaf witnesses generating EVERY ambient vertex below p+1.

The support compression is one actual finite FULL diary C. Every
source image f(u), u<|A|, is <p, so the increasing support rank map
fixes this particular embedding pointwise. Every additional source
survives via the same full meet-preserving factorisation, all
ambient edges/nonedges below p are fixed, and a genuine terminal
leaf of C lies beyond the old exact image.

Crucial OPEN input: the already-existing countable ambient G and the
given genuine embeddings. This does NOT construct the missing relative
absorber prediary, its protected germ profile, bounded selected
forward ranks, or countable-source every-target-flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Given ONE specifically chosen protected finite diary copy in an
ambient full countable diary, together with an arbitrary FINITE family
of other genuine finite diary copies in that same ambient, extract ONE
genuine finite full diary containing them all.

The original chosen copy keeps EXACTLY its original ambient numeric
positions, including every true old split and leaf; the family members
are fully induced, role- and mixed-meet-preserving bounded copies.
The entire old ambient prefix is literal, and a fresh terminal leaf
remains outside the chosen old image. -/
theorem exists_finiteDiary_preserving_one_exact_image_and_family
    {A G : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (hn : 4 ≤ n)
    (DG : RoleDiary G)
    (E : FiniteMeetEmbedding A G n f)
    (p : Nat)
    (hOldBound : ∀ u : Nat, u < n → f u < p)
    (Ds : List FiniteDiaryInput)
    (hCopies : ∀ D : FiniteDiaryInput, D ∈ Ds →
      ∃ h : Nat → Nat, FiniteMeetEmbedding D.graph G D.bound h) :
    ∃ (C : Ordered3Graph Nat) (k : Nat) (g : Nat → Nat),
      FiniteRoleDiaryBlock C k ∧
      p < k ∧
      FiniteBoundedMeetEmbedding A C n k g ∧
      (∀ u : Nat, u < n → g u = f u) ∧
      (∀ D : FiniteDiaryInput, D ∈ Ds →
        ∃ h : Nat → Nat,
          FiniteBoundedMeetEmbedding D.graph C D.bound k h) ∧
      (∀ a b c : Nat, a < b → b < c → c < p →
        (C.edge a b c ↔ G.edge a b c)) ∧
      IsLeaf C (k-1) ∧
      (∀ u : Nat, u < n → g u < k-1) := by
  classical
  obtain ⟨WFamily,hWFamily,hWitnesses⟩ :=
    exists_finiteFamily_leaf_support (G := G) Ds hCopies
  let WOld : Finset Nat :=
    ((Finset.Ico 3 n).filter (fun u => IsLeaf A u)).image f
  have hWOld : ∀ x : Nat, x ∈ WOld → IsLeaf G x := by
    intro x hx
    change x ∈ ((Finset.Ico 3 n).filter (fun u => IsLeaf A u)).image f at hx
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨huFrame,hLeaf⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu3,hun⟩ := Finset.mem_Ico.mp huFrame
    exact (E.leaf_iff u hu3 hun).mpr hLeaf
  let W : Finset Nat := WFamily ∪ WOld
  have hW : ∀ x : Nat, x ∈ W → IsLeaf G x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hfam | hold
    · exact hWFamily x hfam
    · exact hWOld x hold
  obtain ⟨L,hWL,hLeaves,hPrefix⟩ :=
    DG.exists_leafSupport_covering_prefix_and_leaves (p+1) W hW
  let S : Finset Nat := finiteLeafMeetSupport G L
  let C : Ordered3Graph Nat := finiteSupportGraph G S
  let k : Nat := S.card
  let g : Nat → Nat := finiteSupportLift S n f
  have hDiary : FiniteRoleDiaryBlock C k :=
    finiteLeafMeetSupport_is_finiteDiary DG hLeaves
  have hImageLeavesOld : ∀ u : Nat, 3 ≤ u → u < n →
      IsLeaf A u → f u ∈ L := by
    intro u hu3 hun hLeaf
    have hInOld : f u ∈ WOld := by
      change f u ∈ ((Finset.Ico 3 n).filter
        (fun t => IsLeaf A t)).image f
      exact Finset.mem_image.mpr
        ⟨u,Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨hu3,hun⟩,hLeaf⟩,rfl⟩
    exact hWL (Finset.mem_union.mpr (Or.inr hInOld))
  have hRangeOld : ∀ u : Nat, u < n → f u ∈ S := by
    exact FiniteMeetEmbedding.range_subset_leafMeetSupport
      DA E L hImageLeavesOld
  have hG : FiniteMeetEmbedding A C n g :=
    E.through_finiteSupport DA S hRangeOld
  have hBounded : ∀ u : Nat, u < n → g u < k := by
    intro u hu
    exact (finiteSupportLift_spec S n f hRangeOld u hu).1
  have hPK : p < k := by
    have hSpec := finiteSupportRank_spec
      S p (hPrefix p (by omega))
    have hRank := finiteSupportRank_fixed_prefix
      S (p+1) hPrefix p (by omega)
    rw [hRank] at hSpec
    exact hSpec.1
  have hExact : ∀ u : Nat, u < n → g u = f u := by
    intro u hu
    have hR : f u < p+1 := by
      have hb := hOldBound u hu
      omega
    change finiteSupportLift S n f u = f u
    rw [finiteSupportLift_of_lt S n f u hu]
    exact finiteSupportRank_fixed_prefix S (p+1) hPrefix
      (f u) hR
  have hEdges : ∀ a b c : Nat, a < b → b < c → c < p →
      (C.edge a b c ↔ G.edge a b c) := by
    intro a b c hab hbc hc
    have hcK : c < k := by
      have hSpec := finiteSupportRank_spec
        S c (hPrefix c (by omega))
      have hRank := finiteSupportRank_fixed_prefix
        S (p+1) hPrefix c (by omega)
      rw [hRank] at hSpec
      exact hSpec.1
    have hA := finiteSupportIndex_fixed_prefix
      S (p+1) hPrefix a (by omega)
    have hB := finiteSupportIndex_fixed_prefix
      S (p+1) hPrefix b (by omega)
    have hC := finiteSupportIndex_fixed_prefix
      S (p+1) hPrefix c (by omega)
    have hIff := finiteSupportGraph_edge_iff G S a b c hab hbc hcK
    simpa only [C,hA,hB,hC] using hIff
  have hP4 : 4 ≤ p := by
    have hThird : f 2 < f 3 :=
      E.strictMono (by omega : 2 < 3)
    rw [E.marker_two] at hThird
    have hOld3 := hOldBound 3 (by omega)
    omega
  have hFour : 4 ≤ k := by omega
  have hLast : IsLeaf C (k-1) := hDiary.last_is_leaf hFour
  refine ⟨C,k,g,hDiary,hPK,⟨hG,hBounded⟩,hExact,?_,hEdges,
    hLast,?_⟩
  · intro D hD
    obtain ⟨h,Eh,hImages⟩ := hWitnesses D hD
    have hImagesL : ∀ u : Nat, 3 ≤ u → u < D.bound →
        IsLeaf D.graph u → h u ∈ L := by
      intro u hu3 hu hLeaf
      have hInFamily := hImages u hu3 hu hLeaf
      exact hWL (Finset.mem_union.mpr (Or.inl hInFamily))
    have hRangeD : ∀ u : Nat, u < D.bound → h u ∈ S := by
      exact FiniteMeetEmbedding.range_subset_leafMeetSupport
        D.diary Eh L hImagesL
    have hED : FiniteMeetEmbedding D.graph C D.bound
        (finiteSupportLift S D.bound h) :=
      Eh.through_finiteSupport D.diary S hRangeD
    refine ⟨finiteSupportLift S D.bound h,⟨hED,?_⟩⟩
    intro u hu
    exact (finiteSupportLift_spec S D.bound h hRangeD u hu).1
  · intro u hu
    have hLess : g u < p := by
      rw [hExact u hu]
      exact hOldBound u hu
    omega

end DiaryLeafPriority
end ThreeUniformDiaries
