import ThreeUniformDiaries.CanonicalMap
import ThreeUniformDiaries.BranchHypergraph

/-!
# Canonical maps act functorially on finite enumeration branches

A branch vertex is a finite enumeration H of length i+1, marked by i.
Its image under a canonical map F is the prefix of F.mapEnum H through
the newly selected index F.level i.  This is equivalent to the
manuscript's last-vertex successor formula after the ambient type
identities have been proved.

Unlike the infinite-height geometric construction, this definition
works for every already constructed CanonicalMap.  Its composition
law is a genuine consequence of the selected-truncation field,
rather than an extra axiom about the maps on K_I.
-/

namespace ThreeUniformDiaries
namespace CanonicalMap

/-- Canonical map on each vertex of the universal branch hypergraph. -/
noncomputable def mapBranch (F : CanonicalMap)
    (B : EnumerationBranchNode) : EnumerationBranchNode :=
  ⟨F.level B.last,
   (F.mapEnum (B.last + 1) B.enumeration).truncate (F.level B.last + 1)⟩

@[simp] theorem mapBranch_last (F : CanonicalMap)
    (B : EnumerationBranchNode) :
    (F.mapBranch B).last = F.level B.last := rfl

@[simp] theorem id_mapBranch (B : EnumerationBranchNode) :
    (CanonicalMap.id.mapBranch B) = B := by
  cases B with
  | mk i A =>
    change (⟨i, A.truncate (i + 1)⟩ : EnumerationBranchNode) = ⟨i, A⟩
    rw [EnumNode.truncate_self]

/-- A selected prefix map on branch vertices commutes with
composition of the three synchronized coordinate maps. -/
theorem comp_mapBranch (G F : CanonicalMap)
    (B : EnumerationBranchNode) :
    (CanonicalMap.comp G F).mapBranch B =
      G.mapBranch (F.mapBranch B) := by
  cases B with
  | mk i A =>
    let E := F.mapEnum (i + 1) A
    have hc : F.level i + 1 ≤ F.level (i + 1) :=
      Nat.succ_le_of_lt (F.strictMono (Nat.lt_succ_self i))
    have hgc : G.level (F.level i) + 1 ≤
        G.level (F.level i + 1) :=
      Nat.succ_le_of_lt (G.strictMono (Nat.lt_succ_self (F.level i)))
    have ht := G.truncate_compat E hc
    have hp :
        (G.mapEnum (F.level (i + 1)) E).truncate
            (G.level (F.level i) + 1) =
        (G.mapEnum (F.level i + 1)
            (E.truncate (F.level i + 1))).truncate
              (G.level (F.level i) + 1) := by
      rw [ht]
      exact (EnumNode.truncate_truncate
        (G.mapEnum (F.level (i + 1)) E) hgc).symm
    change (⟨G.level (F.level i),
        (G.mapEnum (F.level (i + 1)) E).truncate
          (G.level (F.level i) + 1)⟩ : EnumerationBranchNode) =
      ⟨G.level (F.level i),
        (G.mapEnum (F.level i + 1)
          (E.truncate (F.level i + 1))).truncate
            (G.level (F.level i) + 1)⟩
    exact congrArg (fun z : EnumNode (G.level (F.level i) + 1) =>
        (⟨G.level (F.level i), z⟩ : EnumerationBranchNode)) hp

end CanonicalMap
end ThreeUniformDiaries
