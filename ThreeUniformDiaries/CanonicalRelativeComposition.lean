import ThreeUniformDiaries.CanonicalRelativeCarrier

/-!
# Composition of actual relative K_I canonical branch maps

The condition that a canonical map fixes an initial finite
enumeration is stable under composition even when the first
unprotected level n is shifted. Consequently, composition holds
LITERALLY for the maps of the entire relative branch hypergraph K_I.

This completes the algebraic K_I part of Lemma canonicalcomposition.
The remaining geometric step is to produce an actual strong vector
subtree whose canonical map equals the composite.
-/

namespace ThreeUniformDiaries
namespace CanonicalMap

private theorem level_ge_index (F : CanonicalMap) (n : Nat) :
    n ≤ F.level n := by
  induction n with
  | zero => omega
  | succ k ih =>
      have hs : F.level k + 1 ≤ F.level (k + 1) :=
        Nat.succ_le_of_lt (F.strictMono (Nat.lt_succ_self k))
      omega

/-- Two canonical maps fixing the same protected initial hypergraph
have a composite fixing it; the selected level n may be shifted. -/
theorem comp_fixesRelativeCut
    (G F : CanonicalMap) {n : Nat} (I : EnumNode n)
    (hF : F.FixesRelativeCut I)
    (hG : G.FixesRelativeCut I) :
    (CanonicalMap.comp G F).FixesRelativeCut I := by
  constructor
  · intro j hj
    change G.level (F.level j) = j
    rw [hF.1 j hj, hG.1 j hj]
  · let E := F.mapEnum n I
    have hFn : n ≤ F.level n := level_ge_index F n
    have hGn : n ≤ G.level n := level_ge_index G n
    have hcut : G.mapEnum n (E.truncate n) =
        (G.mapEnum (F.level n) E).truncate (G.level n) :=
      G.truncate_compat E hFn
    change (G.mapEnum (F.level n) E).truncate n = I
    calc
      (G.mapEnum (F.level n) E).truncate n =
          ((G.mapEnum (F.level n) E).truncate (G.level n)).truncate n :=
        (EnumNode.truncate_truncate _ hGn).symm
      _ = (G.mapEnum n (E.truncate n)).truncate n := by
          rw [← hcut]
      _ = (G.mapEnum n I).truncate n := by
          rw [hF.2]
      _ = I := hG.2

/-- The canonical relative branch maps compose at every vertex of K_I.
This is the complete algebraic relative-carrier composition formula,
rather than a conditional branch-layer interface. -/
theorem comp_relativeMapBranch
    (G F : CanonicalMap) {n : Nat} (I : EnumNode n)
    (hF : F.FixesRelativeCut I)
    (hG : G.FixesRelativeCut I)
    (B : RelativeBranchNode I) :
    (CanonicalMap.comp G F).relativeMapBranch I
        (comp_fixesRelativeCut G F I hF hG) B =
      G.relativeMapBranch I hG (F.relativeMapBranch I hF B) := by
  apply Subtype.ext
  change (CanonicalMap.comp G F).mapBranch B.val =
      G.mapBranch (F.mapBranch B.val)
  exact comp_mapBranch G F B.val

end CanonicalMap
end ThreeUniformDiaries
