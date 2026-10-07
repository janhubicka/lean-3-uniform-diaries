import ThreeUniformDiaries.CanonicalMap

/-!
# Type preservation by canonical maps

These are the equality-level forms of clauses (2)--(4) of the manuscript's
canonical-map lemma.  Equality of 1-type nodes and equality of auxiliary-type
nodes are both preserved and reflected because canonical maps commute with
type formation and are injective on every level.
-/

namespace ThreeUniformDiaries
namespace CanonicalMap

/-- Selected hyperedges are preserved exactly by a canonical map. -/
theorem enumTriple_true_iff
    (F : CanonicalMap) {N i j k : Nat} (H : EnumNode N)
    (hij : i < j) (hjk : j < k) (hkN : k < N) :
    H.triple i j k = true ↔
      (F.mapEnum N H).triple (F.level i) (F.level j) (F.level k) = true := by
  rw [F.enum_triple_compat H hij hjk hkN]

/-- Equality of 1-types over a selected cut is preserved and reflected. -/
theorem oneType_eq_iff
    (F : CanonicalMap) {N l u v : Nat} (H : EnumNode N)
    (hlu : l ≤ u) (hlv : l ≤ v) (huN : u < N) (hvN : v < N) :
    H.oneType l u = H.oneType l v ↔
      (F.mapEnum N H).oneType (F.level l) (F.level u) =
        (F.mapEnum N H).oneType (F.level l) (F.level v) := by
  have hu :=
    F.oneType_compat H hlu huN
  have hv :=
    F.oneType_compat H hlv hvN
  rw [← hu, ← hv]
  constructor
  · intro h
    exact congrArg (F.mapOne l) h
  · intro h
    exact F.mapOne_injective l h

/-- Equality of auxiliary types over a selected cut is preserved and
reflected. -/
theorem auxType_eq_iff
    (F : CanonicalMap) {N l u₀ u₁ v₀ v₁ : Nat} (H : EnumNode N)
    (hlu : l ≤ u₀) (hu : u₀ < u₁) (huN : u₁ < N)
    (hlv : l ≤ v₀) (hv : v₀ < v₁) (hvN : v₁ < N) :
    H.auxType l u₀ u₁ = H.auxType l v₀ v₁ ↔
      (F.mapEnum N H).auxType (F.level l) (F.level u₀) (F.level u₁) =
        (F.mapEnum N H).auxType (F.level l) (F.level v₀) (F.level v₁) := by
  have huEq :=
    F.auxType_compat H hlu hu huN
  have hvEq :=
    F.auxType_compat H hlv hv hvN
  rw [← huEq, ← hvEq]
  constructor
  · intro h
    exact congrArg (F.mapAux l) h
  · intro h
    exact F.mapAux_injective l h

/-- Restriction to a selected cut commutes with the canonical map. -/
theorem restriction_eq
    (F : CanonicalMap) {N l : Nat} (H : EnumNode N) (hlN : l ≤ N) :
    F.mapEnum l (H.truncate l) =
      (F.mapEnum N H).truncate (F.level l) :=
  F.truncate_compat H hlN

end CanonicalMap
end ThreeUniformDiaries
