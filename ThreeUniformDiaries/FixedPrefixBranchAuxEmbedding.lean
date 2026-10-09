import ThreeUniformDiaries.FixedPrefixParentSchedule
import ThreeUniformDiaries.FixedPrefixBranchGap
import ThreeUniformDiaries.ExactMeetsFromTypes
import ThreeUniformDiaries.TypeCutTransfer

/-!
# Auxiliary type respect and exact meets for canonical branches fixing I

Choose once a length-first enumeration E of K_I and an inherited-gap
embedding from E.graph into G that is literally the identity below n.
Every H extending I then induces a canonical branch of the *same*
global embedding. Source K_I cut tests and the fixed-prefix omitted
target propagation yield both kinds of type agreement; edge reflection
and first-difference witnesses yield literal meet preservation.
-/

namespace ThreeUniformDiaries
namespace SizeFirstBranchPresentation

variable {n : Nat} {I : EnumNode n} (E : SizeFirstBranchPresentation I)

/-- The induced canonical branch of the fixed-prefix global K_I embedding. -/
noncomputable def fixedBranchEmbedding
    (G : GenericEnumerated3Graph)
    (hKG : E.graph.initialSegment n = G.graph.initialSegment n)
    (hn : 0 < n)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I) :
    Ordered3Graph.Embedding H G.graph := by
  let parent := E.fixedSourceParents hn
  let f := G.fixedInheritedEmbedding E.graph n hKG parent
  let h := E.branchIndex H hI
  refine {
    toFun := fun v => f (h v)
    strictMono := ?_
    edge_iff := ?_
  }
  · exact ((G.fixedInheritedEmbedding_isEmbedding E.graph n hKG parent).1).comp
      (E.branchIndex_strictMono H hI)
  · intro a b c hab hbc
    have hmono : StrictMono h := E.branchIndex_strictMono H hI
    have hedge := (G.fixedInheritedEmbedding_isEmbedding
      E.graph n hKG parent).2.2
    exact (E.graph_branch_edge_iff H hI hab hbc).symm.trans
      (hedge (h a) (h b) (h c) (hmono hab) (hmono hbc))

/-- An induced canonical branch fixes the entire prescribed I-prefix. -/
theorem fixedBranchEmbedding_prefix
    (G : GenericEnumerated3Graph)
    (hKG : E.graph.initialSegment n = G.graph.initialSegment n)
    (hn : 0 < n)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (k : Nat) (hk : k < n) :
    E.fixedBranchEmbedding G hKG hn H hI k = k := by
  change G.fixedInheritedEmbedding E.graph n hKG
    (E.fixedSourceParents hn) (E.branchIndex H hI k) = k
  rw [E.branchIndex_fixed_prefix H hI k hk]
  exact G.fixedInheritedEmbedding_prefix E.graph n hKG
    (E.fixedSourceParents hn) k hk

/-- Singleton type agreement at every original cut is transported
through the fixed-prefix K_I branch to the ambient generic target. -/
theorem fixedBranch_oneAgreement
    (G : GenericEnumerated3Graph)
    (hKG : E.graph.initialSegment n = G.graph.initialSegment n)
    (hn : 0 < n)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (w u v : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hsame : H.SameOneTypeBelow w u v) :
    G.graph.SameOneTypeBelow (E.fixedBranchEmbedding G hKG hn H hI w)
      (E.fixedBranchEmbedding G hKG hn H hI u)
      (E.fixedBranchEmbedding G hKG hn H hI v) := by
  let h := E.branchIndex H hI
  let parent := E.fixedSourceParents hn
  let f := G.fixedInheritedEmbedding E.graph n hKG parent
  change G.graph.SameOneTypeBelow (f (h w)) (f (h u)) (f (h v))
  have hh : GenericEnumerated3Graph.FollowsFixedParents n parent h := by
    constructor
    · exact E.branchIndex_strictMono H hI
    · intro t ht
      exact E.branchIndex_follows_fixedParents hn H hI t ht
  have hmono : StrictMono f :=
    (G.fixedInheritedEmbedding_isEmbedding E.graph n hKG parent).1
  have hedge :=
    (G.fixedInheritedEmbedding_isEmbedding E.graph n hKG parent).2.2
  have hsource : E.graph.SameOneTypeBelow (h w) (h u) (h v) :=
    E.source_oneAgreement_at_index H hI w u v hwu hwv hsame
  have hgap : ∀ x y : Nat, x < y → y < f (h w) →
      ((¬ ∃ a : Nat, f a = x) ∨ (¬ ∃ b : Nat, f b = y)) →
      (G.graph.edge x y (f (h u)) ↔
        G.graph.edge x y (f (h v))) := by
    intro x y hxy hyw hmiss
    apply G.fixed_branch_omitted_oneType E.graph n hKG parent
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

/-- Auxiliary type agreement at every original cut is transported
through the fixed-prefix canonical branch. -/
theorem fixedBranch_auxAgreement
    (G : GenericEnumerated3Graph)
    (hKG : E.graph.initialSegment n = G.graph.initialSegment n)
    (hn : 0 < n)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (w u₀ u₁ v₀ v₁ : Nat)
    (hwu : w ≤ u₀) (hu : u₀ < u₁)
    (hwv : w ≤ v₀) (hv : v₀ < v₁)
    (hsame : H.SameAuxTypeBelow w u₀ u₁ v₀ v₁) :
    G.graph.SameAuxTypeBelow (E.fixedBranchEmbedding G hKG hn H hI w)
      (E.fixedBranchEmbedding G hKG hn H hI u₀)
      (E.fixedBranchEmbedding G hKG hn H hI u₁)
      (E.fixedBranchEmbedding G hKG hn H hI v₀)
      (E.fixedBranchEmbedding G hKG hn H hI v₁) := by
  let h := E.branchIndex H hI
  let parent := E.fixedSourceParents hn
  let f := G.fixedInheritedEmbedding E.graph n hKG parent
  change G.graph.SameAuxTypeBelow
    (f (h w)) (f (h u₀)) (f (h u₁)) (f (h v₀)) (f (h v₁))
  have hh : GenericEnumerated3Graph.FollowsFixedParents n parent h := by
    constructor
    · exact E.branchIndex_strictMono H hI
    · intro t ht
      exact E.branchIndex_follows_fixedParents hn H hI t ht
  have hmono : StrictMono f :=
    (G.fixedInheritedEmbedding_isEmbedding E.graph n hKG parent).1
  have hedge :=
    (G.fixedInheritedEmbedding_isEmbedding E.graph n hKG parent).2.2
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
    · apply G.fixed_branch_omitted_auxType E.graph n hKG parent
        h hh u₀ u₁ x hu (lt_of_lt_of_le hxw
          (hmono.monotone (hh.1.monotone hwu)))
      intro i hi
      exact hx ⟨i, hi⟩
    · apply G.fixed_branch_omitted_auxType E.graph n hKG parent
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

/-- A fixed-prefix canonical branch preserves and reflects singleton
and auxiliary type agreement at every selected cut. -/
theorem fixedBranch_auxTypeRespecting
    (G : GenericEnumerated3Graph)
    (hKG : E.graph.initialSegment n = G.graph.initialSegment n)
    (hn : 0 < n)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I) :
    (E.fixedBranchEmbedding G hKG hn H hI).AuxTypeRespecting := by
  let e := E.fixedBranchEmbedding G hKG hn H hI
  constructor
  · intro w u v hwu hwv
    constructor
    · intro hsource
      exact E.fixedBranch_oneAgreement G hKG hn H hI w u v hwu hwv hsource
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
      exact E.fixedBranch_auxAgreement G hKG hn H hI
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

/-- In particular the canonical branch preserves the literal capped
singleton meet levels in the target, not just their agreement relation. -/
theorem fixedBranch_oneMeet_eq
    (G : GenericEnumerated3Graph)
    (hKG : E.graph.initialSegment n = G.graph.initialSegment n)
    (hn : 0 < n)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (u v : Nat) :
    G.graph.oneMeetLevel
      (E.fixedBranchEmbedding G hKG hn H hI u)
      (E.fixedBranchEmbedding G hKG hn H hI v) =
      E.fixedBranchEmbedding G hKG hn H hI (H.oneMeetLevel u v) :=
  (E.fixedBranchEmbedding G hKG hn H hI).oneMeetLevel_eq_of_auxTypeRespecting
    (E.fixedBranch_auxTypeRespecting G hKG hn H hI) u v

/-- The literal capped auxiliary meet is preserved as well. -/
theorem fixedBranch_auxMeet_eq
    (G : GenericEnumerated3Graph)
    (hKG : E.graph.initialSegment n = G.graph.initialSegment n)
    (hn : 0 < n)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (u₀ u₁ v₀ v₁ : Nat) (hu : u₀ < u₁) (hv : v₀ < v₁) :
    G.graph.auxMeetLevel
      (E.fixedBranchEmbedding G hKG hn H hI u₀)
      (E.fixedBranchEmbedding G hKG hn H hI u₁)
      (E.fixedBranchEmbedding G hKG hn H hI v₀)
      (E.fixedBranchEmbedding G hKG hn H hI v₁) =
      E.fixedBranchEmbedding G hKG hn H hI
        (H.auxMeetLevel u₀ u₁ v₀ v₁) :=
  (E.fixedBranchEmbedding G hKG hn H hI).auxMeetLevel_eq_of_auxTypeRespecting
    (E.fixedBranch_auxTypeRespecting G hKG hn H hI)
    u₀ u₁ v₀ v₁ hu hv

end SizeFirstBranchPresentation
end ThreeUniformDiaries
