import ThreeUniformDiaries.DiaryPrediaryDefinition

/-!
# A V2 obstruction to identifying an early split in the raw flip tree

At a genuine 2-split, the diary V2 coherence condition says
that all positively incident ordered leaf pairs have identical
full pair types below the split. In particular their marker-1
auxiliary bits agree.

Therefore two induced diary copies whose positive pairs have
OPPOSITE marker-1 bits cannot be amalgamated in a pre-diary if
they identify the 2-split vertex and fix marker 1.

This theorem is independent of pre-diary completion and of
cross-branch edge additions. The finite source and two genuine
nine-vertex flips witnessing its hypotheses are recorded in
notes/flip_root_obstruction_and_ordered_sum.tex in the
3-uniform-diaries manuscript repository.

No claim about construction of a replacement flip tree is made.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RolePrediary

open Ordered3Graph

variable {H K L : Ordered3Graph Nat}

/-- Immediate consequence of V2: the auxiliary marker-1 bit
on positively incident leaf pairs is an invariant of a shared
2-split vertex, including the marker-1 cut inside the type. -/
theorem positive_pair_marker_one_agrees
    (P : RolePrediary H)
    (m a b c d : Nat)
    (hm : IsTwoSplit H m)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hPosAB : H.edge m a b)
    (hPosCD : H.edge m c d) :
    H.edge 1 a b ↔ H.edge 1 c d := by
  have hPair :=
    P.two_split_coherent m a b c d
      hm hab hcd ha hb hc hd hPosAB hPosCD
  have hMark : 1 < m := by
    have hbound := hm.1
    omega
  exact hPair.2.2 hMark

/-- Two ordered induced embeddings fixing marker 1 and
identifying their 2-split cannot carry opposite marker-1
orientations on positive ordered leaf pairs.

This is the abstract mathematical obstruction to the
chronological flip-prefix branch-amalgamation claim. -/
theorem no_common_twoSplit_of_opposite_positive_markers
    (P : RolePrediary H)
    (f : Embedding K H) (g : Embedding L H)
    (m a b : Nat)
    (hma : m < a) (hab : a < b)
    (hOneF : f 1 = 1) (hOneG : g 1 = 1)
    (hSameSplit : f m = g m)
    (hSplit : IsTwoSplit H (f m))
    (hFa : IsLeaf H (f a)) (hFb : IsLeaf H (f b))
    (hGa : IsLeaf H (g a)) (hGb : IsLeaf H (g b))
    (hPosF : K.edge m a b)
    (hPosG : L.edge m a b)
    (hMarkerF : K.edge 1 a b)
    (hMarkerG : ¬ L.edge 1 a b) :
    False := by
  have hPosInF : H.edge (f m) (f a) (f b) :=
    (f.edge_iff hma hab).mp hPosF
  have hPosInG : H.edge (f m) (g a) (g b) := by
    rw [hSameSplit]
    exact (g.edge_iff hma hab).mp hPosG
  have hOneA : 1 < a := by
    have hmOne : 1 < m := by
      by_contra hmNot
      have hmSmall : m ≤ 1 := Nat.le_of_not_gt hmNot
      have hImageLe : f m ≤ f 1 :=
        f.strictMono.monotone hmSmall
      have hImageLarge : 3 ≤ f m := hSplit.1
      rw [hOneF] at hImageLe
      omega
    exact lt_trans hmOne hma
  have hMarkerInF : H.edge 1 (f a) (f b) := by
    have h := (f.edge_iff hOneA hab).mp hMarkerF
    simpa only [hOneF] using h
  have hMarkerNotG : ¬ H.edge 1 (g a) (g b) := by
    intro h
    have h' : H.edge (g 1) (g a) (g b) := by
      simpa only [hOneG] using h
    exact hMarkerG ((g.edge_iff hOneA hab).mpr h')
  have hSameMarker :=
    P.positive_pair_marker_one_agrees
      (f m) (f a) (f b) (g a) (g b)
      hSplit (f.strictMono hab) (g.strictMono hab)
      hFa hFb hGa hGb hPosInF hPosInG
  exact hMarkerNotG (hSameMarker.mp hMarkerInF)

end RolePrediary
end DiaryLeafPriority
end ThreeUniformDiaries
