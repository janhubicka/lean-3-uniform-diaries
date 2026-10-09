import ThreeUniformDiaries.TypeRepresentation
import ThreeUniformDiaries.VectorTree

/-!
# Prefix compatibility of finite singleton and auxiliary type nodes

When forming the meet-closed coordinate sets in the finite converse
(Aemb), the type of a vertex or pair over a later cut restricts to its
type over every earlier cut. This file isolates the elementary
truncation equalities and their agreement interpretations.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- A later singleton-type node restricts to the singleton type
already present at the earlier cut. -/
theorem oneType_truncate {N l k u : Nat}
    (H : EnumNode N) (hkl : k ≤ l) :
    (H.oneType l u).truncate k = H.oneType k u := by
  apply OneNode.ext_pairs
  funext i j
  by_cases hjk : j < k
  · have hjl : j < l := lt_of_lt_of_le hjk hkl
    simp [OneNode.truncate, EnumNode.oneType, hjk, hjl]
  · simp [OneNode.truncate, EnumNode.oneType, hjk]

/-- Auxiliary-type nodes also commute with restriction to an earlier
cut, without an assumption that the cuts are consecutive. -/
theorem auxType_truncate {N l k u v : Nat}
    (H : EnumNode N) (hkl : k ≤ l) :
    (H.auxType l u v).truncate k = H.auxType k u v := by
  apply AuxNode.ext_bits
  funext i
  by_cases hik : i < k
  · have hil : i < l := lt_of_lt_of_le hik hkl
    simp [AuxNode.truncate, EnumNode.auxType, hik, hil]
  · simp [AuxNode.truncate, EnumNode.auxType, hik]

/-- A meet of two singleton-type nodes sees precisely their edge
agreement below the earlier cut. -/
theorem oneType_prefix_eq_iff {N l k u v : Nat}
    (H : EnumNode N) (hkl : k ≤ l) :
    (H.oneType l u).truncate k =
      (H.oneType l v).truncate k ↔
      H.toOrdered3Graph.SameOneTypeBelow k u v := by
  rw [H.oneType_truncate (u := u) hkl,
    H.oneType_truncate (u := v) hkl]
  exact H.oneType_eq_iff_sameOneTypeBelow

/-- Likewise auxiliary-type prefixes agree exactly when the
corresponding edge bits agree below the cut. -/
theorem auxType_prefix_eq_iff {N l k u₀ u₁ v₀ v₁ : Nat}
    (H : EnumNode N) (hkl : k ≤ l) :
    (H.auxType l u₀ u₁).truncate k =
      (H.auxType l v₀ v₁).truncate k ↔
      H.toOrdered3Graph.SameAuxTypeBelow k u₀ u₁ v₀ v₁ := by
  rw [H.auxType_truncate (u := u₀) (v := u₁) hkl,
    H.auxType_truncate (u := v₀) (v := v₁) hkl]
  exact H.auxType_eq_iff_sameAuxTypeBelow

end EnumNode
end ThreeUniformDiaries
