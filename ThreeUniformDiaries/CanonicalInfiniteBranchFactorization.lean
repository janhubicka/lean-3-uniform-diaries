import ThreeUniformDiaries.CanonicalInfiniteImage
import ThreeUniformDiaries.CanonicalRelativeCarrier
import ThreeUniformDiaries.BranchHypergraph
import ThreeUniformDiaries.RelativeBranchHypergraph

/-!
# Factorization of the actual infinite canonical branch map

The canonical image graph has exact initial segments at every selected
target level. The universal branch map of a canonical map therefore
commutes *on the nose* with the branch representation of the full
countable image. In a protected relative K_I context, the countable
image also has precisely the same prescribed initial segment I.

These facts connect the infinite E0/E1/E2 canonical maps to the
relative K_I factorization in the manuscript's Lemma auxtypeemb.
They require neither an assumed branch-code compatibility field nor
a source-specific factorization axiom.
-/

namespace ThreeUniformDiaries

namespace CanonicalMap

/-- The branch image of any infinite source vertex is exactly the
corresponding branch vertex in the coherent countable image. -/
theorem mapBranch_branchNode
    (F : CanonicalMap) (H : Ordered3Graph Nat) (v : Nat) :
    F.mapBranch (H.branchNode v) =
      (F.imageGraph H).branchNode (F.level v) := by
  have hlev : F.level v + 1 ≤ F.level (v + 1) :=
    Nat.succ_le_of_lt (F.strictMono (Nat.lt_succ_self v))
  have hprefix :=
    (F.imageGraph H).initialSegment_truncate hlev
  rw [F.imageGraph_initialSegment_eq H (v + 1)] at hprefix
  change
    (⟨F.level v,
      (F.mapEnum (v + 1) (H.initialSegment (v + 1))).truncate
        (F.level v + 1)⟩ : EnumerationBranchNode) =
    ⟨F.level v,
      (F.imageGraph H).initialSegment (F.level v + 1)⟩
  exact congrArg
    (fun A : EnumNode (F.level v + 1) =>
      (⟨F.level v, A⟩ : EnumerationBranchNode)) hprefix

private theorem branch_level_ge_index (F : CanonicalMap) (n : Nat) :
    n ≤ F.level n := by
  induction n with
  | zero => omega
  | succ k ih =>
      have hs : F.level k + 1 ≤ F.level (k + 1) :=
        Nat.succ_le_of_lt (F.strictMono (Nat.lt_succ_self k))
      omega

/-- The full countable canonical image has the same initial hypergraph
I whenever the canonical map preserves the protected relative cut. -/
theorem imageGraph_initialCut
    (F : CanonicalMap) (H : Ordered3Graph Nat)
    {n : Nat} (I : EnumNode n)
    (hI : H.initialSegment n = I)
    (hfix : F.FixesRelativeCut I) :
    (F.imageGraph H).initialSegment n = I := by
  have hn : n ≤ F.level n := F.branch_level_ge_index n
  have hprefix :=
    (F.imageGraph H).initialSegment_truncate hn
  rw [F.imageGraph_initialSegment_eq H n, hI] at hprefix
  exact hprefix.symm.trans hfix.2

/-- Exact commutation of the relative branch code and infinite
canonical image for *every* source vertex (not only finite coding
test configurations). -/
theorem relativeMapBranch_branchNode
    (F : CanonicalMap) (H : Ordered3Graph Nat)
    {n : Nat} (I : EnumNode n)
    (hI : H.initialSegment n = I)
    (hfix : F.FixesRelativeCut I) (v : Nat) :
    (F.relativeMapBranch I hfix
        (H.relativeBranchNode I hI v)).val =
      ((F.imageGraph H).relativeBranchNode I
        (F.imageGraph_initialCut H I hI hfix)
        (F.level v)).val := by
  change F.mapBranch (H.branchNode v) =
    (F.imageGraph H).branchNode (F.level v)
  exact F.mapBranch_branchNode H v

end CanonicalMap

end ThreeUniformDiaries
