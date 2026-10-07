import ThreeUniformDiaries.CanonicalTypes
import ThreeUniformDiaries.TypeRepresentation

/-!
# Canonical maps preserve type agreement at selected cuts

Combine the concrete type representations with canonical-map compatibility.
The result is stated in the original hypergraph predicates rather than in
the internal type-node representation.  Exact *meet-level* preservation
requires a further successor/first-difference argument and is not claimed
here.
-/

namespace ThreeUniformDiaries
namespace CanonicalMap

/-- Canonical maps preserve hyperedges on increasing triples of selected
vertices, as an equivalence of the original hypergraph edge predicates. -/
theorem preserves_selected_edges
    (F : CanonicalMap) {N i j k : Nat} (H : EnumNode N)
    (hij : i < j) (hjk : j < k) (hkN : k < N) :
    H.toOrdered3Graph.edge i j k ↔
      (F.mapEnum N H).toOrdered3Graph.edge (F.level i) (F.level j) (F.level k) := by
  calc
    H.toOrdered3Graph.edge i j k ↔ H.triple i j k = true :=
      H.toOrdered3Graph_edge
    _ ↔ (F.mapEnum N H).triple (F.level i) (F.level j) (F.level k) = true :=
      F.enumTriple_true_iff H hij hjk hkN
    _ ↔ (F.mapEnum N H).toOrdered3Graph.edge (F.level i) (F.level j) (F.level k) :=
      ((F.mapEnum N H).toOrdered3Graph_edge).symm

/-- Equality of singleton types at a selected cut is both preserved and
reflected. -/
theorem preserves_selected_one_agreement
    (F : CanonicalMap) {N l u v : Nat} (H : EnumNode N)
    (hlu : l ≤ u) (hlv : l ≤ v) (huN : u < N) (hvN : v < N) :
    H.toOrdered3Graph.SameOneTypeBelow l u v ↔
      (F.mapEnum N H).toOrdered3Graph.SameOneTypeBelow
        (F.level l) (F.level u) (F.level v) := by
  calc
    H.toOrdered3Graph.SameOneTypeBelow l u v ↔
        H.oneType l u = H.oneType l v :=
      (H.oneType_eq_iff_sameOneTypeBelow).symm
    _ ↔
        (F.mapEnum N H).oneType (F.level l) (F.level u) =
          (F.mapEnum N H).oneType (F.level l) (F.level v) :=
      F.oneType_eq_iff H hlu hlv huN hvN
    _ ↔
        (F.mapEnum N H).toOrdered3Graph.SameOneTypeBelow
          (F.level l) (F.level u) (F.level v) :=
      (F.mapEnum N H).oneType_eq_iff_sameOneTypeBelow

/-- Auxiliary type agreement at a selected cut is both preserved and
reflected. -/
theorem preserves_selected_aux_agreement
    (F : CanonicalMap) {N l u₀ u₁ v₀ v₁ : Nat} (H : EnumNode N)
    (hlu : l ≤ u₀) (hu : u₀ < u₁) (huN : u₁ < N)
    (hlv : l ≤ v₀) (hv : v₀ < v₁) (hvN : v₁ < N) :
    H.toOrdered3Graph.SameAuxTypeBelow l u₀ u₁ v₀ v₁ ↔
      (F.mapEnum N H).toOrdered3Graph.SameAuxTypeBelow
        (F.level l) (F.level u₀) (F.level u₁)
        (F.level v₀) (F.level v₁) := by
  calc
    H.toOrdered3Graph.SameAuxTypeBelow l u₀ u₁ v₀ v₁ ↔
        H.auxType l u₀ u₁ = H.auxType l v₀ v₁ :=
      (H.auxType_eq_iff_sameAuxTypeBelow).symm
    _ ↔
        (F.mapEnum N H).auxType (F.level l) (F.level u₀) (F.level u₁) =
          (F.mapEnum N H).auxType (F.level l) (F.level v₀) (F.level v₁) :=
      F.auxType_eq_iff H hlu hu huN hlv hv hvN
    _ ↔
        (F.mapEnum N H).toOrdered3Graph.SameAuxTypeBelow
          (F.level l) (F.level u₀) (F.level u₁)
          (F.level v₀) (F.level v₁) :=
      (F.mapEnum N H).auxType_eq_iff_sameAuxTypeBelow

end CanonicalMap
end ThreeUniformDiaries
