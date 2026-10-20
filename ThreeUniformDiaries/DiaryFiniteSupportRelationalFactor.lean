import ThreeUniformDiaries.DiaryFiniteSupportInverseRank

/-!
# Induced relational factorisation through a finite support

A supplied finite meet embedding A -> G with all source vertices
retained in S factors relationally through the increasing induced
restriction of G to S. The induced finite map is the canonical
rank lift: its restriction to [0,n) is exactly the inverse of
the support enumeration on f's image; outside n it is extended
monotonically into an irrelevant fresh tail.

This file proves exact edges AND nonedges and all three literal
marker roles. Numerical singleton and full pair meets require
separate first-disagreement proofs and are NOT asserted here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A G : Ordered3Graph Nat} {S : Finset Nat}
variable {n : Nat} {f : Nat → Nat}

/-- Edges and nonedges of the supplied finite source agree with
those in the finite induced support under the actual inverse rank
map. The result is not conditional on a target source diary axiom. -/
theorem finiteSupportLift_edge_iff
    (E : FiniteMeetEmbedding A G n f)
    (hRange : ∀ u, u < n → f u ∈ S)
    (a b c : Nat) (hab : a < b) (hbc : b < c)
    (hc : c < n) :
    (finiteSupportGraph G S).edge
      (finiteSupportLift S n f a)
      (finiteSupportLift S n f b)
      (finiteSupportLift S n f c) ↔ A.edge a b c := by
  let g := finiteSupportLift S n f
  have ha : a < n := by omega
  have hb : b < n := by omega
  have ga := finiteSupportLift_spec S n f hRange a ha
  have gb := finiteSupportLift_spec S n f hRange b hb
  have gc := finiteSupportLift_spec S n f hRange c hc
  have hg : StrictMono g :=
    finiteSupportLift_strictMono S n f E.strictMono hRange
  have hga : g a < g b := hg hab
  have hgb : g b < g c := hg hbc
  change (finiteSupportGraph G S).edge (g a) (g b) (g c) ↔ A.edge a b c
  calc
    _ ↔ G.edge (finiteSupportIndex S (g a))
        (finiteSupportIndex S (g b))
        (finiteSupportIndex S (g c)) :=
          finiteSupportGraph_edge_iff G S (g a) (g b) (g c)
            hga hgb gc.1
    _ ↔ A.edge a b c := by
      simpa only [ga.2,gb.2,gc.2] using
        E.edge_iff a b c hab hbc hc

/-- A genuine source nonmarker remains a genuine target nonmarker
under finite compression. -/
theorem finiteSupportLift_ge_three
    (E : FiniteMeetEmbedding A G n f)
    (hRange : ∀ u, u < n → f u ∈ S)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (u : Nat) (hu3 : 3 ≤ u) (hu : u < n) :
    3 ≤ finiteSupportLift S n f u := by
  have hSrc : 3 ≤ f u := by
    have hMono := E.strictMono (show 2 < u by omega)
    rw [E.marker_two] at hMono
    omega
  have hspec := finiteSupportLift_spec S n f hRange u hu
  apply finiteSupportIndex_ge_three_of_image S
    (finiteSupportLift S n f u) h0 h1 h2 hspec.1
  simpa only [hspec.2] using hSrc

/-- The literal source leaf role is reflected by the finite
induced target on every source nonmarker vertex in the frame. -/
theorem finiteSupportLift_leaf_iff
    (E : FiniteMeetEmbedding A G n f)
    (hRange : ∀ u, u < n → f u ∈ S)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (u : Nat) (hu3 : 3 ≤ u) (hu : u < n) :
    IsLeaf (finiteSupportGraph G S) (finiteSupportLift S n f u) ↔
      IsLeaf A u := by
  have hspec := finiteSupportLift_spec S n f hRange u hu
  have hIndex3 := finiteSupportLift_ge_three
    E hRange h0 h1 h2 u hu3 hu
  calc
    IsLeaf (finiteSupportGraph G S) (finiteSupportLift S n f u)
        ↔ IsLeaf G (finiteSupportIndex S (finiteSupportLift S n f u)) :=
          finiteSupportGraph_leaf_iff
            (G := G) (S := S) h0 h1 h2
            (finiteSupportLift S n f u) hIndex3 hspec.1
    _ ↔ IsLeaf G (f u) := by rw [hspec.2]
    _ ↔ IsLeaf A u := E.leaf_iff u hu3 hu

/-- Exact one-split marker-role reflection on the compressed
source image. -/
theorem finiteSupportLift_oneSplit_iff
    (E : FiniteMeetEmbedding A G n f)
    (hRange : ∀ u, u < n → f u ∈ S)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (u : Nat) (hu3 : 3 ≤ u) (hu : u < n) :
    IsOneSplit (finiteSupportGraph G S) (finiteSupportLift S n f u) ↔
      IsOneSplit A u := by
  have hspec := finiteSupportLift_spec S n f hRange u hu
  have hIndex3 := finiteSupportLift_ge_three
    E hRange h0 h1 h2 u hu3 hu
  calc
    IsOneSplit (finiteSupportGraph G S) (finiteSupportLift S n f u)
        ↔ IsOneSplit G (finiteSupportIndex S (finiteSupportLift S n f u)) :=
          finiteSupportGraph_oneSplit_iff
            (G := G) (S := S) h0 h1 h2
            (finiteSupportLift S n f u) hIndex3 hspec.1
    _ ↔ IsOneSplit G (f u) := by rw [hspec.2]
    _ ↔ IsOneSplit A u := E.oneSplit_iff u hu3 hu

/-- Exact two-split marker-role reflection on the compressed
source image. -/
theorem finiteSupportLift_twoSplit_iff
    (E : FiniteMeetEmbedding A G n f)
    (hRange : ∀ u, u < n → f u ∈ S)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (u : Nat) (hu3 : 3 ≤ u) (hu : u < n) :
    IsTwoSplit (finiteSupportGraph G S) (finiteSupportLift S n f u) ↔
      IsTwoSplit A u := by
  have hspec := finiteSupportLift_spec S n f hRange u hu
  have hIndex3 := finiteSupportLift_ge_three
    E hRange h0 h1 h2 u hu3 hu
  calc
    IsTwoSplit (finiteSupportGraph G S) (finiteSupportLift S n f u)
        ↔ IsTwoSplit G (finiteSupportIndex S (finiteSupportLift S n f u)) :=
          finiteSupportGraph_twoSplit_iff
            (G := G) (S := S) h0 h1 h2
            (finiteSupportLift S n f u) hIndex3 hspec.1
    _ ↔ IsTwoSplit G (f u) := by rw [hspec.2]
    _ ↔ IsTwoSplit A u := E.twoSplit_iff u hu3 hu

end DiaryLeafPriority
end ThreeUniformDiaries
