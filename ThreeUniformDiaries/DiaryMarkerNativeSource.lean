import ThreeUniformDiaries.DiaryMarkerCutOrientation
import ThreeUniformDiaries.DiaryFusedThreeTailPairs
import ThreeUniformDiaries.DiaryCommonFinitePointedSource

/-!
# One genuine native three-tail ATR source for each diary orientation class

At marker cut 3, source lexicographic orientation of two ordered
leaf pairs is equivalent to their full 2-type agreement. Every
distinct diary leaf pair has a proper singleton meet with
one-split role at level >=3, so its minimal envelope at this
cut is THREE-tail (prefix + one-split + two leaves).

The already verified role-based pointed shape theorem identifies
the actual compressed enumerated hypergraphs of any two leaf
pairs in the same orientation class even when the
type-respecting diary-to-generic map skips levels.

We package this source equality as SameFinitePointedSource at
cut psi(3): the common source, two genuinely finite ATR codes,
prefix-fixing and final endpoints.

The open global synchronisation problem must produce ONE finite
generic gadget combining the positive and negative sources.
This theorem does not assume the missing gadget amalgamation.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Equal source orientations give a common native finite ATR
pointed source at the image of diary marker cut 3. -/
theorem sameFinitePointedSource_of_diary_same_lex_at_three
    (G : GenericEnumerated3Graph)
    {H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hlex : LexEarlier H a b ↔ LexEarlier H c d) :
    SameFinitePointedSource G (ψ 3)
      (ψ a) (ψ b) (ψ c) (ψ d) := by
  classical
  let j := ψ 3
  have ha3 : 3 ≤ a := by have hh := ha.1; omega
  have hc3 : 3 ≤ c := by have hh := hc.1; omega
  have hpair : H.SameTwoTypeBelow 3 a b c d :=
    (D.leaf_sameTwoTypeBelow_three_iff_lex
      a b c d hab hcd ha hb hc hd).mpr hlex
  have hma : IsOneSplit H (H.oneMeetLevel a b) :=
    D.singleton_meets a b ha hb (ne_of_lt hab)
  have hmc : IsOneSplit H (H.oneMeetLevel c d) :=
    D.singleton_meets c d hc hd (ne_of_lt hcd)
  have hcase : 3 ≤ H.oneMeetLevel a b := hma.1
  have hcaseCD : 3 ≤ H.oneMeetLevel c d := hmc.1
  let E₀ : FinitePointedEnvelope G.graph j (ψ a) (ψ b) :=
    FinitePointedEnvelope.ofRoleThreeTail D ψ hψ
      3 a b (by omega) ha3 hab ha hb hcase
  let E₁ : FinitePointedEnvelope G.graph j (ψ c) (ψ d) :=
    FinitePointedEnvelope.ofRoleThreeTail D ψ hψ
      3 c d (by omega) hc3 hcd hc hd hcaseCD
  have hsource : E₀.finiteEnum = E₁.finiteEnum := by
    change
      ((G.graph.pullback
        (threeTailInsertion j (ψ (H.oneMeetLevel a b))
          (ψ a) (ψ b))).initialSegment (j+3)) =
      ((G.graph.pullback
        (threeTailInsertion j (ψ (H.oneMeetLevel c d))
          (ψ c) (ψ d))).initialSegment (j+3))
    exact D.three_tail_finiteEnum_eq_of_same_leaf_twoType
      ψ hψ 3 a b c d (by omega) ha3 hc3 hab hcd
      ha hb hc hd hpair hcase
  let A : ProtectedSource j := threeVertexSource j E₀.finiteEnum
  have hA : A ∈ smallSourceUniverse j :=
    threeVertexSource_mem j E₀.finiteEnum
  let e₀ : A.Code G := E₀.finiteATRCode
  have hf : FiniteAuxEmbedding E₀.finiteEnum.toOrdered3Graph
      G.graph E₁.enumerate (j+3) := by
    rw [hsource]
    exact E₁.finite_aux_embedding.of_initialSegment
  let e₁ : A.Code G :=
    FiniteAuxEmbeddingImage.ofFiniteAuxEmbedding E₁.enumerate hf
  have he₀ : A.FixesPrefix G e₀ := by
    intro t ht
    exact E₀.finiteATRCode_fix_prefix t ht
  have he₁ : A.FixesPrefix G e₁ := by
    intro t ht
    change E₁.enumerate t.val = t.val
    exact E₁.protected_prefix t.val ht
  have hp₀ : e₀.image A.penultimateIndex = ψ a := by
    change E₀.enumerate (j+1) = ψ a
    exact threeTailInsertion_first j
      (ψ (H.oneMeetLevel a b)) (ψ a) (ψ b)
  have hl₀ : e₀.image A.lastIndex = ψ b := by
    change E₀.enumerate (j+2) = ψ b
    exact threeTailInsertion_second j
      (ψ (H.oneMeetLevel a b)) (ψ a) (ψ b)
  have hp₁ : e₁.image A.penultimateIndex = ψ c := by
    change E₁.enumerate (j+1) = ψ c
    exact threeTailInsertion_first j
      (ψ (H.oneMeetLevel c d)) (ψ c) (ψ d)
  have hl₁ : e₁.image A.lastIndex = ψ d := by
    change E₁.enumerate (j+2) = ψ d
    exact threeTailInsertion_second j
      (ψ (H.oneMeetLevel c d)) (ψ c) (ψ d)
  exact ⟨⟨A, hA, e₀, e₁, he₀, he₁, hp₀, hl₀, hp₁, hl₁⟩⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
