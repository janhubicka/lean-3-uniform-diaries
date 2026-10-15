import ThreeUniformDiaries.DiaryChosenPreembedding

/-!
# Exact singleton meets of all leaf pairs under the chosen candidate

For two source leaves u,v there are only two cases:

* If u=v, their singleton type meet is the vertex itself, both
  before and after the genuinely induced stabilised embedding.
* If u≠v, source S1 identifies the singleton meet m as a one-split.
  The 1-split marker role is disjoint from both leaf roles, so
  m<u,v. The verified full I2 witness-independence theorem says
  that the genuine target singleton meet of the two image leaves
  equals the candidate pre-embedding's chosen image of m.

This proves the complete singleton-meet condition for leaf pairs,
including diagonal pairs. It does not assume any arbitrary gap-
preserving property of the original unordered outer map.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The ordinary singleton meet with itself equals the original
vertex, because the same singleton type agrees through its cap. -/
theorem oneMeetLevel_self_eq (H : Ordered3Graph Nat) (a : Nat) :
    H.oneMeetLevel a a = a := by
  classical
  have hUpper : H.oneMeetLevel a a ≤ a := by
    simpa only [min_self] using H.oneMeetLevel_le_min a a
  have hSelf : H.SameOneTypeBelow a a a := by
    intro x y hxy hy
    rfl
  have hLower : a ≤ H.oneMeetLevel a a :=
    Nat.le_findGreatest (by simp) hSelf
  exact Nat.le_antisymm hUpper hLower

end Ordered3Graph

namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

variable {H : Ordered3Graph Nat}

/-- Every singleton type meet of two SOURCE LEAVES is preserved
by the proposed chosen diary pre-embedding when evaluated on the
target images of those leaves. The original outer map is allowed
to be unordered and the source's generic type-respecting image
may omit arbitrarily many enumeration levels. -/
theorem chosenPreembedding_preserves_leaf_oneMeet
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (u v : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v) :
    let φ := stabilisedSource G K F ψ
    K.oneMeetLevel (φ u) (φ v) =
      D.chosenPreembedding G K F ψ (H.oneMeetLevel u v) := by
  let φ := stabilisedSource G K F ψ
  change K.oneMeetLevel (φ u) (φ v) =
    D.chosenPreembedding G K F ψ (H.oneMeetLevel u v)
  by_cases hEq : u = v
  · subst v
    rw [H.oneMeetLevel_self_eq, K.oneMeetLevel_self_eq,
      D.chosenPreembedding_leaf G K F ψ u hu]
  · let m := H.oneMeetLevel u v
    have hrole : IsOneSplit H m := D.singleton_meets u v hu hv hEq
    have hcap : m ≤ min u v := H.oneMeetLevel_le_min u v
    have hnu : m ≠ u := by
      intro h
      have hs : IsOneSplit H u := by simpa only [h] using hrole
      exact hu.2.1 hs.2.1
    have hnv : m ≠ v := by
      intro h
      have hs : IsOneSplit H v := by simpa only [h] using hrole
      exact hv.2.1 hs.2.1
    have hmu : m < u := by omega
    have hmv : m < v := by omega
    have hValue : D.oneSplitTargetImage G K F ψ m hrole =
      K.oneMeetLevel (φ u) (φ v) :=
      D.oneSplitTargetImage_eq_any_witness
        G K F ψ hψ m u v hrole hu hv hmu hmv rfl
    calc
      K.oneMeetLevel (φ u) (φ v) =
        D.oneSplitTargetImage G K F ψ m hrole := hValue.symm
      _ = D.chosenPreembedding G K F ψ m :=
        (D.chosenPreembedding_oneSplit G K F ψ m hrole).symm

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
