import ThreeUniformDiaries.DiaryFlipBranchAmalgam

/-!
# Cross-branch edge additions preserving every original flip copy

The raw tree-of-flips edge relation is the union of branch edges.
It is not a pre-diary: incomparable leaves need extra Devlin
markers. The first indispensable invariant for any completion
is that each original diary flip remains an INDUCED copy.

We provide a general operation adding an arbitrary candidate
edge predicate only on triples that are not jointly realised
along a single branch. This guarantees preservation and
reflection of the induced relation on each branch, including
nonedges.

CAVEAT: inducedness does NOT imply preservation of the leaf
singleton and pair-type meets against new off-branch witnesses.
V1/V2 coherence and those meet calculations are still separate
completion obligations. Nor does this module construct a
satisfactory Devlin marker assignment.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary
namespace FlipFamily

variable {A : Ordered3Graph Nat} {ι : Type*}

/-- The three prefix-tree nodes occur at increasing levels
on at least one common flip branch, independently of whether
that branch contains an edge on the triple. -/
def BranchSpansTriple
    (T : FlipFamily A ι)
    (X Y Z : FlipNode) : Prop :=
  ∃ (i : ι) (x y z : Nat),
    x < y ∧ y < z ∧
    T.node i x = X ∧ T.node i y = Y ∧ T.node i z = Z

/-- An arbitrary extension predicate is used ONLY on triples
outside every individual flip branch. It cannot modify any
branch edge or nonedge, but may introduce cross-branch
Devlin markers and other completion edges. -/
def withCrossBranchEdges
    (T : FlipFamily A ι)
    (extra : FlipNode → FlipNode → FlipNode → Prop) :
    Ordered3Graph FlipNode where
  edge X Y Z :=
    (T.branchAmalgam).edge X Y Z ∨
      (¬ T.BranchSpansTriple X Y Z ∧ extra X Y Z)

/-- Exact, unconditional preservation/reflection of all
increasing triples in every original flip branch. -/
theorem withCrossBranchEdges_induced
    (T : FlipFamily A ι)
    (extra : FlipNode → FlipNode → FlipNode → Prop)
    (i : ι) (x y z : Nat) (hxy : x < y) (hyz : y < z) :
    (T.withCrossBranchEdges extra).edge
      (T.node i x) (T.node i y) (T.node i z) ↔
    (T.graph i).edge x y z := by
  constructor
  · rintro (hOld | ⟨hOutside, hExtra⟩)
    · exact (T.branchAmalgam_edge_iff i x y z hxy hyz).mp hOld
    · exact False.elim
        (hOutside ⟨i, x, y, z, hxy, hyz, rfl, rfl, rfl⟩)
  · intro h
    exact Or.inl
      ((T.branchAmalgam_edge_iff i x y z hxy hyz).mpr h)

/-- On any triple lying entirely on one branch, the extension
agrees literally with the raw branch amalgam. -/
theorem withCrossBranchEdges_eq_on_branch
    (T : FlipFamily A ι)
    (extra : FlipNode → FlipNode → FlipNode → Prop)
    (i : ι) (x y z : Nat) (hxy : x < y) (hyz : y < z) :
    (T.withCrossBranchEdges extra).edge
      (T.node i x) (T.node i y) (T.node i z) ↔
      (T.branchAmalgam).edge
        (T.node i x) (T.node i y) (T.node i z) := by
  exact (T.withCrossBranchEdges_induced extra i x y z hxy hyz).trans
    (T.branchAmalgam_edge_iff i x y z hxy hyz).symm

end FlipFamily
end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
