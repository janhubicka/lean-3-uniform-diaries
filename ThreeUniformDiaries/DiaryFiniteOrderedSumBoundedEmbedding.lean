import ThreeUniformDiaries.DiaryFiniteOrderedSumCarrier

/-!
# Bounded support and global induced right embedding of finite sums

The carrier of two bounded source edge tables has no hyperedges
outside the combined finite support n+(m-3). This makes the
right translated copy an actual induced increasing embedding
on all Nat, not merely an edge equivalence restricted to c<m:
both source and target edges involving later vertices vanish.

This sharpens the checked finite raw ordered-sum construction
without asserting its global V/E/S pre-diary axioms, which
remain separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

def finiteTwoBlockLength (n m : Nat) : Nat := n + (m - 3)

/-- Every genuine right nonmarker vertex below m maps into the
finite combined carrier. -/
theorem rightBlockImage_lt_finiteTwoBlockLength
    (n m v : Nat)
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hv3 : 3 ≤ v) (hvm : v < m) :
    rightBlockImage n v < finiteTwoBlockLength n m := by
  have hnot : ¬ v < 3 := by omega
  simp only [rightBlockImage, if_neg hnot, finiteTwoBlockLength]
  omega

/-- Every source right vertex at or beyond its finite edge table
maps at or beyond the complete finite carrier. -/
theorem rightBlockImage_ge_finiteTwoBlockLength
    (n m v : Nat)
    (hm : 3 ≤ m) (hvm : m ≤ v) :
    finiteTwoBlockLength n m ≤ rightBlockImage n v := by
  have hnot : ¬ v < 3 := by omega
  simp only [rightBlockImage, if_neg hnot, finiteTwoBlockLength]
  omega

/-- The actual raw two-block ordered-sum carrier is itself a
finite bounded increasing edge table of the expected size.
This is independent of all cross-marker orientation choices. -/
theorem finiteTwoBlockCarrier_finiteFrame
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) :
    FiniteDiaryEdgeFrame
      (finiteTwoBlockCarrier H K n m bits)
      (finiteTwoBlockLength n m) := by
  refine ⟨by
    unfold finiteTwoBlockLength
    have hn3 := FH.length_ge_three
    omega, ?_⟩
  intro a b c he
  have hOrdered :=
    finiteTwoBlockCarrier_edge_ordered FH FK bits a b c he
  rcases he with hLeft | hRight | hCross
  · have hSupp := FH.edge_support a b c hLeft.1
    have hc3 : 3 ≤ c := hSupp.2.2.1
    have hcn : c < n := hLeft.2
    refine ⟨hOrdered.1,hOrdered.2,hc3,?_⟩
    unfold finiteTwoBlockLength
    omega
  · obtain ⟨a',b',c',hK,hcm,_ha,_hb,hc⟩ := hRight
    have hc3 : 3 ≤ c' := (FK.edge_support a' b' c' hK).2.2.1
    subst c
    have hBound :=
      rightBlockImage_lt_finiteTwoBlockLength n m c'
        FH.length_ge_three FK.length_ge_three hc3 hcm
    have hImage3 : 3 ≤ rightBlockImage n c' := by
      have hge := rightBlockImage_nonmarker_ge n c'
        FH.length_ge_three hc3
      have hn3 := FH.length_ge_three
      omega
    exact ⟨hOrdered.1,hOrdered.2,hImage3,hBound⟩
  · obtain ⟨u,v,_hu3,_hun,_huLeaf,hv3,hvm,_hvLeaf,_hy,hz,_hbit⟩ := hCross
    have hBound :=
      rightBlockImage_lt_finiteTwoBlockLength n m v
        FH.length_ge_three FK.length_ge_three hv3 hvm
    have hImage3 : 3 ≤ rightBlockImage n v := by
      have hge := rightBlockImage_nonmarker_ge n v
        FH.length_ge_three hv3
      have hn3 := FH.length_ge_three
      omega
    subst c
    exact ⟨hOrdered.1,hOrdered.2,hImage3,hBound⟩

/-- Exact induced right-copy relation without any cut restriction
on the source third vertex. When c>=m both edge predicates are
false, because the carrier has no edges outside its finite
support, and the right map sends c outside that support. -/
theorem finiteTwoBlockCarrier_right_edge_iff_all
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (a b c : Nat) :
    (finiteTwoBlockCarrier H K n m bits).edge
      (rightBlockImage n a) (rightBlockImage n b)
      (rightBlockImage n c) ↔ K.edge a b c := by
  by_cases hcm : c < m
  · exact finiteTwoBlockCarrier_right_edge_iff
      FH FK bits a b c hcm
  · have hge : m ≤ c := by omega
    have hSourceFalse : ¬ K.edge a b c := by
      intro he
      have hbound := (FK.edge_support a b c he).2.2.2
      omega
    have hTargetFalse :
        ¬ (finiteTwoBlockCarrier H K n m bits).edge
          (rightBlockImage n a) (rightBlockImage n b)
          (rightBlockImage n c) := by
      intro he
      have hBound :=
        ((finiteTwoBlockCarrier_finiteFrame FH FK bits).edge_support
          _ _ _ he).2.2.2
      have hBeyond :=
        rightBlockImage_ge_finiteTwoBlockLength n m c
          FK.length_ge_three hge
      omega
    exact iff_of_false hTargetFalse hSourceFalse

/-- The translated finite right block is an induced increasing
embedding of the *entire* source ordered edge predicate.
The source itself is bounded so no off-block source edges are
lost, and no target edge fills an old source nonedge. -/
noncomputable def finiteTwoBlockRightEmbedding
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) :
    Ordered3Graph.Embedding K (finiteTwoBlockCarrier H K n m bits) where
  toFun := rightBlockImage n
  strictMono := rightBlockImage_strictMono n FH.length_ge_three
  edge_iff := by
    intro a b c _hab _hbc
    exact (finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits a b c).symm

end DiaryLeafPriority
end ThreeUniformDiaries
