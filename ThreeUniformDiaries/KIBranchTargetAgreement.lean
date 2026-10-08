import ThreeUniformDiaries.SizeFirstParentSchedule
import ThreeUniformDiaries.BranchGapPropagation
import ThreeUniformDiaries.TypeCutTransfer

/-!
# Full target agreement along branches of the inherited K_I embedding

At a selected cut f(h(w)), every target test splits into two cases.
If all test vertices are selected, source agreement at the actual
size-first K_I index follows from SizeFirstSourceTests. If at least
one vertex is omitted from the global K_I image, inherited-gap
propagation along the parent chain compares the target edge bits.

This file proves those two cases fit together to establish singleton
and auxiliary type agreement at every branch cut. It uses a general
size-first K_I presentation, so constructing an actual presentation
and fixing a prescribed initial segment remain separate interfaces.
-/

namespace ThreeUniformDiaries
namespace SizeFirstBranchPresentation

variable {n : Nat} {I : EnumNode n} (E : SizeFirstBranchPresentation I)
variable (G : GenericEnumerated3Graph)

private abbrev inheritedMap : Nat → Nat :=
  G.inheritedEmbedding E.graph E.sourceParentSchedule

private theorem inheritedMap_mono :
    StrictMono (E.inheritedMap G) :=
  (G.exists_countable_inherited_embedding E.graph E.sourceParentSchedule).1

private theorem inheritedMap_edge (a b c : Nat) (hab : a < b) (hbc : b < c) :
    E.graph.edge a b c ↔
      G.graph.edge (E.inheritedMap G a)
        (E.inheritedMap G b) (E.inheritedMap G c) :=
  (G.exists_countable_inherited_embedding E.graph E.sourceParentSchedule).2 a b c hab hbc

private theorem index_follows_parents
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I) :
    GenericEnumerated3Graph.FollowsParents E.sourceParentSchedule
      (E.branchIndex H hI) := by
  exact E.branchIndex_follows_sourceParents H hI

/-- The new generic copy of K_I agrees on singleton types below
every image of a canonical source branch cut. -/
theorem inherited_branch_oneAgreement
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (w u v : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hsame : H.SameOneTypeBelow w u v) :
    G.graph.SameOneTypeBelow
      (E.inheritedMap G (E.branchIndex H hI w))
      (E.inheritedMap G (E.branchIndex H hI u))
      (E.inheritedMap G (E.branchIndex H hI v)) := by
  let f := E.inheritedMap G
  let h := E.branchIndex H hI
  have hf : StrictMono f := E.inheritedMap_mono G
  have hh : StrictMono h := E.branchIndex_strictMono H hI
  have hparent :
      GenericEnumerated3Graph.FollowsParents E.sourceParentSchedule h :=
    E.index_follows_parents H hI
  have hsource : E.graph.SameOneTypeBelow (h w) (h u) (h v) :=
    E.source_oneAgreement_at_index H hI w u v hwu hwv hsame
  have hgap :
      ∀ x y : Nat, x < y → y < f (h w) →
        ((¬ ∃ a : Nat, f a = x) ∨ (¬ ∃ b : Nat, f b = y)) →
        (G.graph.edge x y (f (h u)) ↔
         G.graph.edge x y (f (h v))) := by
    intro x y hxy hyw hmiss
    exact G.inherited_branch_omitted_oneType E.graph E.sourceParentSchedule
      h hparent w u v hwu hwv x y hxy hyw hmiss
  exact E.graph.oneTypeAgreement_transfer G.graph f hf
    (E.inheritedMap_edge G) (h w) (h u) (h v)
    (hh.monotone hwu) (hh.monotone hwv) hsource hgap

/-- Likewise every auxiliary test below an image branch cut agrees.
Omitted target vertices give non-edges through both selected pairs. -/
theorem inherited_branch_auxAgreement
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (w u₀ u₁ v₀ v₁ : Nat)
    (hwu : w ≤ u₀) (hu : u₀ < u₁)
    (hwv : w ≤ v₀) (hv : v₀ < v₁)
    (hsame : H.SameAuxTypeBelow w u₀ u₁ v₀ v₁) :
    G.graph.SameAuxTypeBelow
      (E.inheritedMap G (E.branchIndex H hI w))
      (E.inheritedMap G (E.branchIndex H hI u₀))
      (E.inheritedMap G (E.branchIndex H hI u₁))
      (E.inheritedMap G (E.branchIndex H hI v₀))
      (E.inheritedMap G (E.branchIndex H hI v₁)) := by
  let f := E.inheritedMap G
  let h := E.branchIndex H hI
  have hf : StrictMono f := E.inheritedMap_mono G
  have hh : StrictMono h := E.branchIndex_strictMono H hI
  have hparent :
      GenericEnumerated3Graph.FollowsParents E.sourceParentSchedule h :=
    E.index_follows_parents H hI
  have hsource : E.graph.SameAuxTypeBelow
      (h w) (h u₀) (h u₁) (h v₀) (h v₁) :=
    E.source_auxAgreement_at_index H hI
      w u₀ u₁ v₀ v₁ hwu hu hwv hv hsame
  have hgap :
      ∀ x : Nat, x < f (h w) → (¬ ∃ a : Nat, f a = x) →
      ¬ G.graph.edge x (f (h u₀)) (f (h u₁)) ∧
      ¬ G.graph.edge x (f (h v₀)) (f (h v₁)) := by
    intro x hx hmiss
    have hleft : x < f (h u₀) :=
      lt_of_lt_of_le hx ((hf.comp hh).monotone hwu)
    have hright : x < f (h v₀) :=
      lt_of_lt_of_le hx ((hf.comp hh).monotone hwv)
    exact ⟨G.inherited_branch_omitted_auxType E.graph E.sourceParentSchedule
        h hparent u₀ u₁ x hu hleft hmiss,
      G.inherited_branch_omitted_auxType E.graph E.sourceParentSchedule
        h hparent v₀ v₁ x hv hright hmiss⟩
  exact E.graph.auxTypeAgreement_transfer G.graph f hf
    (E.inheritedMap_edge G) (h w) (h u₀) (h u₁) (h v₀) (h v₁)
    (hh.monotone hwu) (hh hu) (hh.monotone hwv) (hh hv)
    hsource hgap

end SizeFirstBranchPresentation
end ThreeUniformDiaries
