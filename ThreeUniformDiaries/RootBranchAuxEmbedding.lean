import ThreeUniformDiaries.SizeFirstParentSchedule
import ThreeUniformDiaries.BranchGapPropagation
import ThreeUniformDiaries.TypeCutTransfer

/-!
# Auxiliary type agreement on canonical branches of the root-based K_I embedding

The global countable inherited embedding of K_I need not itself preserve
all auxiliary types.  We only need its restriction to each canonical branch.
Tests at selected target vertices are handled by the indexed source K_I
agreement lemmas; tests at vertices omitted from the entire K_I image are
handled by inherited gap propagation along the canonical predecessor
schedule.

This is the root-based construction. Preserving an arbitrary prescribed
initial segment requires a separate fixed-prefix branch argument.
-/

namespace ThreeUniformDiaries
namespace SizeFirstBranchPresentation

variable {n : Nat} {I : EnumNode n} (E : SizeFirstBranchPresentation I)

/-- Composition of the canonical branch with the root-based inherited
embedding of the indexed relative branch hypergraph. -/
noncomputable def rootBranchEmbedding
    (G : GenericEnumerated3Graph)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I) :
    Ordered3Graph.Embedding H G.graph where
  toFun := fun v =>
    G.inheritedEmbedding E.graph E.sourceParentSchedule
      (E.branchIndex H hI v)
  strictMono :=
    ((G.exists_countable_inherited_embedding E.graph
      E.sourceParentSchedule).1).comp
      (E.branchIndex_strictMono H hI)
  edge_iff := by
    intro a b c hab hbc
    let h := E.branchIndex H hI
    let f := G.inheritedEmbedding E.graph E.sourceParentSchedule
    have hmono : StrictMono h := E.branchIndex_strictMono H hI
    have hedge := (G.exists_countable_inherited_embedding
      E.graph E.sourceParentSchedule).2
    exact (E.graph_branch_edge_iff H hI hab hbc).symm.trans
      (hedge (h a) (h b) (h c) (hmono hab) (hmono hbc))

/-- Every singleton-type agreement of the original hypergraph is
preserved below the selected target cut of its canonical branch. -/
theorem rootBranch_oneAgreement
    (G : GenericEnumerated3Graph)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (w u v : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hsame : H.SameOneTypeBelow w u v) :
    G.graph.SameOneTypeBelow (E.rootBranchEmbedding G H hI w)
      (E.rootBranchEmbedding G H hI u)
      (E.rootBranchEmbedding G H hI v) := by
  let h := E.branchIndex H hI
  let parent := E.sourceParentSchedule
  let f := G.inheritedEmbedding E.graph parent
  change G.graph.SameOneTypeBelow (f (h w)) (f (h u)) (f (h v))
  have hh : GenericEnumerated3Graph.FollowsParents parent h :=
    E.branchIndex_follows_sourceParents H hI
  have hmono : StrictMono f :=
    (G.exists_countable_inherited_embedding E.graph parent).1
  have hedge :=
    (G.exists_countable_inherited_embedding E.graph parent).2
  have hsource : E.graph.SameOneTypeBelow (h w) (h u) (h v) :=
    E.source_oneAgreement_at_index H hI w u v hwu hwv hsame
  have hgap : ∀ x y : Nat, x < y → y < f (h w) →
      ((¬ ∃ a : Nat, f a = x) ∨ (¬ ∃ b : Nat, f b = y)) →
      (G.graph.edge x y (f (h u)) ↔
        G.graph.edge x y (f (h v))) := by
    intro x y hxy hyw hmiss
    apply G.inherited_branch_omitted_oneType E.graph parent
      h hh w u v x y hwu hwv hxy hyw
    rcases hmiss with hx | hy
    · left
      intro i hi
      exact hx ⟨i, hi⟩
    · right
      intro i hi
      exact hy ⟨i, hi⟩
  exact Ordered3Graph.oneTypeAgreement_transfer E.graph G.graph f
    hmono (fun a b c hab hbc => hedge a b c hab hbc)
    (h w) (h u) (h v)
    (hh.1.monotone hwu) (hh.1.monotone hwv)
    hsource hgap

/-- Auxiliary-type agreement on each canonical branch uses the
source K_I auxiliary tests together with zero edges at globally
omitted target vertices.  The selected K_I tests need not be zero. -/
theorem rootBranch_auxAgreement
    (G : GenericEnumerated3Graph)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (w u₀ u₁ v₀ v₁ : Nat)
    (hwu : w ≤ u₀) (hu : u₀ < u₁)
    (hwv : w ≤ v₀) (hv : v₀ < v₁)
    (hsame : H.SameAuxTypeBelow w u₀ u₁ v₀ v₁) :
    G.graph.SameAuxTypeBelow (E.rootBranchEmbedding G H hI w)
      (E.rootBranchEmbedding G H hI u₀)
      (E.rootBranchEmbedding G H hI u₁)
      (E.rootBranchEmbedding G H hI v₀)
      (E.rootBranchEmbedding G H hI v₁) := by
  let h := E.branchIndex H hI
  let parent := E.sourceParentSchedule
  let f := G.inheritedEmbedding E.graph parent
  change G.graph.SameAuxTypeBelow (f (h w))
    (f (h u₀)) (f (h u₁)) (f (h v₀)) (f (h v₁))
  have hh : GenericEnumerated3Graph.FollowsParents parent h :=
    E.branchIndex_follows_sourceParents H hI
  have hmono : StrictMono f :=
    (G.exists_countable_inherited_embedding E.graph parent).1
  have hedge :=
    (G.exists_countable_inherited_embedding E.graph parent).2
  have hsource : E.graph.SameAuxTypeBelow
      (h w) (h u₀) (h u₁) (h v₀) (h v₁) :=
    E.source_auxAgreement_at_index H hI w u₀ u₁ v₀ v₁
      hwu hu hwv hv hsame
  have hzero : ∀ x : Nat, x < f (h w) →
      (¬ ∃ a : Nat, f a = x) →
      ¬ G.graph.edge x (f (h u₀)) (f (h u₁)) ∧
      ¬ G.graph.edge x (f (h v₀)) (f (h v₁)) := by
    intro x hxw hx
    constructor
    · apply G.inherited_branch_omitted_auxType E.graph parent
        h hh u₀ u₁ x hu (lt_of_lt_of_le hxw
          (hmono.monotone (hh.1.monotone hwu)))
      intro i hi
      exact hx ⟨i, hi⟩
    · apply G.inherited_branch_omitted_auxType E.graph parent
        h hh v₀ v₁ x hv (lt_of_lt_of_le hxw
          (hmono.monotone (hh.1.monotone hwv)))
      intro i hi
      exact hx ⟨i, hi⟩
  exact Ordered3Graph.auxTypeAgreement_transfer E.graph G.graph f
    hmono (fun a b c hab hbc => hedge a b c hab hbc)
    (h w) (h u₀) (h u₁) (h v₀) (h v₁)
    (hh.1.monotone hwu) (hh.1 hu)
    (hh.1.monotone hwv) (hh.1 hv)
    hsource hzero

/-- The root-based canonical branch is an aux-type-respecting induced
embedding at every selected cut. -/
theorem rootBranch_auxTypeRespecting
    (G : GenericEnumerated3Graph)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I) :
    (E.rootBranchEmbedding G H hI).AuxTypeRespecting := by
  let e := E.rootBranchEmbedding G H hI
  constructor
  · intro w u v hwu hwv
    constructor
    · intro hsource
      exact E.rootBranch_oneAgreement G H hI w u v hwu hwv hsource
    · intro htarget a b hab hbw
      have hbu : b < u := lt_of_lt_of_le hbw hwu
      have hbv : b < v := lt_of_lt_of_le hbw hwv
      calc
        H.edge a b u ↔ G.graph.edge (e a) (e b) (e u) :=
          e.edge_iff hab hbu
        _ ↔ G.graph.edge (e a) (e b) (e v) :=
          htarget (e.strictMono hab) (e.strictMono hbw)
        _ ↔ H.edge a b v := (e.edge_iff hab hbv).symm
  · intro w u₀ u₁ v₀ v₁ hwu hu hwv hv
    constructor
    · intro hsource
      exact E.rootBranch_auxAgreement G H hI
        w u₀ u₁ v₀ v₁ hwu hu hwv hv hsource
    · intro htarget a haw
      have hau : a < u₀ := lt_of_lt_of_le haw hwu
      have hav : a < v₀ := lt_of_lt_of_le haw hwv
      calc
        H.edge a u₀ u₁ ↔ G.graph.edge (e a) (e u₀) (e u₁) :=
          e.edge_iff hau hu
        _ ↔ G.graph.edge (e a) (e v₀) (e v₁) :=
          htarget (e.strictMono haw)
        _ ↔ H.edge a v₀ v₁ := (e.edge_iff hav hv).symm

end SizeFirstBranchPresentation
end ThreeUniformDiaries
