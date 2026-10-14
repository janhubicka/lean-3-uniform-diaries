import ThreeUniformDiaries.DiaryChosenPreembedding

/-!
# Diary roles and leaf relations of the witness-chosen candidate

Assume the target K itself is a full role-based diary and the
unordered outer embedding F lands entirely in its leaf set.
The proposed pre-embedding, already proved strictly increasing,
is now seen to preserve the three nonmarker roles:

* Leaves map to leaves because the composed embedding lands in
  the original leaf image of F.
* The target singleton meet of two distinct chosen leaves is a
  one-split by target S1.
* The target full pair meet of two chosen ordered leaf pairs is
  a two-split by target S2. Its strict predecessor placement
  rules out BOTH the capped case and marker 1.

The restriction of the candidate to source leaves is the genuine
induced ordered embedding. These are exactly the role and leaf-
relation components of the diary pre-embedding definition.
The global leaf-type meet check at marker 1 and orientation/flip
synchronisation are independent remaining issues.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Capped singleton meet of a vertex with itself. -/
theorem oneMeetLevel_self_nat (H : Ordered3Graph Nat) (u : Nat) :
    H.oneMeetLevel u u = u := by
  have hupper : H.oneMeetLevel u u ≤ u := by
    simpa only [min_self] using H.oneMeetLevel_le_min u u
  have hsame : H.SameOneTypeBelow u u u := by
    intro x y hxy hy
    rfl
  have hlower : u ≤ H.oneMeetLevel u u :=
    (H.oneMeetLevel_ge_iff_sameOneTypeBelow
      u u u (by omega) (by omega)).mpr hsame
  exact Nat.le_antisymm hupper hlower

end Ordered3Graph

namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

variable {H : Ordered3Graph Nat}

/-- Every vertex of the source, when sent through the original
stabilised ordered embedding, lands in a target leaf as soon
as the original unordered embedding has leaf-valued range. -/
theorem stabilisedSource_lands_in_leaves
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    {H : Ordered3Graph Nat}
    (ψ : Embedding H G.graph) (t : Nat) :
    IsLeaf K (stabilisedSource G K F ψ t) := by
  change IsLeaf K (stabilisedOrdered G K F (ψ t))
  rw [stabilisedOrdered_apply G K F (ψ t)]
  exact hFleaf _

/-- Leaf roles of the complete candidate. -/
theorem chosenPreembedding_preserves_leaf_role
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (ψ : Embedding H G.graph)
    (i : Nat) (hi : IsLeaf H i) :
    IsLeaf K (D.chosenPreembedding G K F ψ i) := by
  rw [D.chosenPreembedding_leaf G K F ψ i hi]
  exact stabilisedSource_lands_in_leaves G K F hFleaf ψ i

/-- The image of a source one-split has the target one-split
role. The two chosen source leaves are distinct because their
singleton meet is STRICTLY before both leaves. -/
theorem chosenPreembedding_preserves_oneSplit_role
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K)
    (ψ : Embedding H G.graph)
    (i : Nat) (hi : IsOneSplit H i) :
    IsOneSplit K (D.chosenPreembedding G K F ψ i) := by
  let φ := stabilisedSource G K F ψ
  let w := D.chosenOneSplitWitness i hi
  have hDistinct : w.u ≠ w.v := by
    intro heq
    have hdiag : H.oneMeetLevel w.u w.u = w.u :=
      H.oneMeetLevel_self_nat w.u
    have hsplit : H.oneMeetLevel w.u w.u = i := by
      simpa only [← heq] using w.meet_eq
    omega
  have hDifferentImages : φ w.u ≠ φ w.v := by
    intro h
    exact hDistinct (φ.strictMono.injective h)
  have hU : IsLeaf K (φ w.u) :=
    stabilisedSource_lands_in_leaves G K F hFleaf ψ w.u
  have hV : IsLeaf K (φ w.v) :=
    stabilisedSource_lands_in_leaves G K F hFleaf ψ w.v
  have hTarget : IsOneSplit K
      (K.oneMeetLevel (φ w.u) (φ w.v)) :=
    E.singleton_meets (φ w.u) (φ w.v) hU hV hDifferentImages
  rw [D.chosenPreembedding_oneSplit G K F ψ i hi]
  exact hTarget

/-- At a source two-split, target S2 forces the chosen full
pair meet to be a target two-split. Its placement is after 2,
and strictly before both first leaves, excluding the other S2
alternatives exactly. -/
theorem chosenPreembedding_preserves_twoSplit_role
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i : Nat) (hi : IsTwoSplit H i) :
    IsTwoSplit K (D.chosenPreembedding G K F ψ i) := by
  let φ := stabilisedSource G K F ψ
  let w := D.chosenTwoSplitWitness i hi
  let t := D.twoSplitTargetImage G K F ψ i hi
  have hPlace := D.twoSplitTargetImage_interval G K F ψ hψ i hi
  have hLower : i-1 ≤ φ (i-1) :=
    strictMono_nat_ge_id φ φ.strictMono (i-1)
  have hLate : 2 < t := by
    have hiBig := hi.1
    have hLp : φ (i-1) < t := hPlace.1
    omega
  have hUpper : t ≤ φ i := hPlace.2
  have hBeforeA : t < φ w.a :=
    lt_of_le_of_lt hUpper (φ.strictMono w.hia)
  have hBeforeC : t < φ w.c :=
    lt_of_le_of_lt hUpper (φ.strictMono w.hic)
  have hNotCapped : t ≠ min (φ w.a) (φ w.c) :=
    ne_of_lt (lt_min hBeforeA hBeforeC)
  have hA : IsLeaf K (φ w.a) :=
    stabilisedSource_lands_in_leaves G K F hFleaf ψ w.a
  have hB : IsLeaf K (φ w.b) :=
    stabilisedSource_lands_in_leaves G K F hFleaf ψ w.b
  have hC : IsLeaf K (φ w.c) :=
    stabilisedSource_lands_in_leaves G K F hFleaf ψ w.c
  have hD : IsLeaf K (φ w.d) :=
    stabilisedSource_lands_in_leaves G K F hFleaf ψ w.d
  have hCases := E.pair_meets
    (φ w.a) (φ w.b) (φ w.c) (φ w.d)
    (φ.strictMono w.hab) (φ.strictMono w.hcd)
    hA hB hC hD
  change t = min (φ w.a) (φ w.c) ∨
    t = 1 ∨ IsTwoSplit K t at hCases
  have hRole : IsTwoSplit K t := by
    rcases hCases with hCap | hOne | hTwo
    · exact False.elim (hNotCapped hCap)
    · omega
    · exact hTwo
  rw [D.chosenPreembedding_twoSplit G K F ψ i hi]
  exact hRole

/-- The leaf restriction of the candidate is a genuine INDUCED
embedding: relation reflection is included, not only preservation. -/
theorem chosenPreembedding_leaf_edge_iff
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph)
    (a b c : Nat) (hab : a < b) (hbc : b < c)
    (ha : IsLeaf H a) (hb : IsLeaf H b) (hc : IsLeaf H c) :
    H.edge a b c ↔
      K.edge (D.chosenPreembedding G K F ψ a)
        (D.chosenPreembedding G K F ψ b)
        (D.chosenPreembedding G K F ψ c) := by
  rw [D.chosenPreembedding_leaf G K F ψ a ha,
    D.chosenPreembedding_leaf G K F ψ b hb,
    D.chosenPreembedding_leaf G K F ψ c hc]
  exact (stabilisedSource G K F ψ).edge_iff hab hbc

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
