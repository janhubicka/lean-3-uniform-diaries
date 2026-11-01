import ThreeUniformDiaries.DiaryUpperBoundFiniteAuxBridge
import ThreeUniformDiaries.DiaryFiniteLeafMeetCompleteReduct

/-!
# Track A: exact finite ATR factorisation of a leaf-generated diary support

This is the *assembly lemma* for the upper-bound factorisation. It is
conditional only on exact numerical S1/S2 meet preservation along a
strictly increasing total extension of the actual finite support index.
The full finite induced-diary-to-ATR bridge is integrated on main;
this module does not duplicate its marker or mixed-meet proofs.

All remaining requirements of a genuine finite auxiliary embedding
are proved from:
- the checked finite V/E/S diary extraction;
- marker/role reflection under induced finite support compression;
- the new complete finite induced-leaf-preembedding -> finite-ATR
  theorem from Track A PR #995.

The missing diary-specific hypotheses here are EXACTLY the two
selected-leaf numeric meet identities (including repeats and
reversed leaf order for one-meets), and construction of a total
strictly increasing support enumerator. The parallel S1/S2 transport
PRs #987/#988 and support-index PR #996 address these respectively.

This theorem does not infer arbitrary mixed-pair type preservation
from mere type-respectingness; that is supplied by PR #995 from
inducedness and the V/E/S axioms. No unavoidability or final diary
Ramsey theorem is used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

variable {G : Ordered3Graph Nat}

/-- A generated finite full diary support is an INDUCED finite
hypergraph on its genuine indices. Any total f agreeing with the
support enumeration on these indices reflects all its bounded
edges and nonedges, not merely edges among leaves. -/
theorem finiteLeafMeetSupport_totalMap_induced
    (L : Finset Nat) (f : Nat → Nat)
    (hIndex : ∀ u : Nat, u < (finiteLeafMeetSupport G L).card →
      f u = finiteSupportIndex (finiteLeafMeetSupport G L) u)
    (a b c : Nat) (hab : a < b) (hbc : b < c)
    (hcn : c < (finiteLeafMeetSupport G L).card) :
    G.edge (f a) (f b) (f c) ↔
      (finiteSupportGraph G (finiteLeafMeetSupport G L)).edge a b c := by
  have han : a < (finiteLeafMeetSupport G L).card := by omega
  have hbn : b < (finiteLeafMeetSupport G L).card := by omega
  rw [hIndex a han, hIndex b hbn, hIndex c hcn]
  exact (finiteSupportGraph_edge_iff
    G (finiteLeafMeetSupport G L) a b c hab hbc hcn).symm

/-- Once the *leaf-only* meet equations and a total strictly
increasing index map are given, the finite generated support
is a legitimate induced leaf-preembedding into its ambient diary.
No mixed-meet conclusion is assumed. -/
theorem finiteLeafMeetSupport_totalMap_preembedding
    (D : RoleDiary G) (L : Finset Nat)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (f : Nat → Nat) (hf : StrictMono f)
    (hIndex : ∀ u : Nat, u < (finiteLeafMeetSupport G L).card →
      f u = finiteSupportIndex (finiteLeafMeetSupport G L) u)
    (hOne : ∀ u v : Nat,
      3 ≤ u → u < (finiteLeafMeetSupport G L).card →
      3 ≤ v → v < (finiteLeafMeetSupport G L).card →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) u →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) v →
      G.oneMeetLevel (f u) (f v) =
        f ((finiteSupportGraph G (finiteLeafMeetSupport G L)).oneMeetLevel u v))
    (hTwo : ∀ a b c d : Nat,
      a < b → c < d →
      3 ≤ a → a < (finiteLeafMeetSupport G L).card →
      3 ≤ b → b < (finiteLeafMeetSupport G L).card →
      3 ≤ c → c < (finiteLeafMeetSupport G L).card →
      3 ≤ d → d < (finiteLeafMeetSupport G L).card →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) a →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) b →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) c →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) d →
      G.twoMeetLevel (f a) (f b) (f c) (f d) =
        f ((finiteSupportGraph G (finiteLeafMeetSupport G L)).twoMeetLevel a b c d)) :
    FiniteLeafPreembedding
      (finiteSupportGraph G (finiteLeafMeetSupport G L)) G
      (finiteLeafMeetSupport G L).card
      (f (finiteLeafMeetSupport G L).card + 1) f := by
  let S := finiteLeafMeetSupport G L
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker G L 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker G L 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker G L 2 (by omega)
  obtain ⟨hCard,hZero,hOneMarker,hTwoMarker⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  have hCardActual : 3 ≤ (finiteLeafMeetSupport G L).card := by
    simpa only [S] using hCard
  refine {
    strictMono := hf
    marker_zero := ?_
    marker_one := ?_
    marker_two := ?_
    image_bound := ?_
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := hOne
    leaf_twoMeet := hTwo
  }
  · rw [hIndex 0 (by omega)]
    exact hZero
  · rw [hIndex 1 (by omega)]
    exact hOneMarker
  · rw [hIndex 2 (by omega)]
    exact hTwoMarker
  · intro u hu
    have hlt := hf hu
    omega
  · intro u hu3 hun
    have hRoleLeaf :=
      finiteSupportGraph_leaf_iff
        (G := G) (S := S) h0 h1 h2 u hu3 hun
    have hRoleOne :=
      finiteSupportGraph_oneSplit_iff
        (G := G) (S := S) h0 h1 h2 u hu3 hun
    have hRoleTwo :=
      finiteSupportGraph_twoSplit_iff
        (G := G) (S := S) h0 h1 h2 u hu3 hun
    rw [hIndex u hun]
    exact ⟨hRoleLeaf.symm, hRoleOne.symm, hRoleTwo.symm⟩
  · intro a b c hab hbc hcn _ _ _
    exact finiteLeafMeetSupport_totalMap_induced
      (G := G) L f hIndex a b c hab hbc hcn

/-- The genuine finite auxiliary-type-respecting embedding on
the compressed source support, conditional ONLY on the exact
leaf-only one- and two-meet table along its actual increasing
enumeration. All mixed and marker cases are discharged by the
full finite induced diary bridge, not postulated. -/
theorem finiteLeafMeetSupport_totalMap_finiteAuxEmbedding
    (D : RoleDiary G) (L : Finset Nat)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (f : Nat → Nat) (hf : StrictMono f)
    (hIndex : ∀ u : Nat, u < (finiteLeafMeetSupport G L).card →
      f u = finiteSupportIndex (finiteLeafMeetSupport G L) u)
    (hOne : ∀ u v : Nat,
      3 ≤ u → u < (finiteLeafMeetSupport G L).card →
      3 ≤ v → v < (finiteLeafMeetSupport G L).card →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) u →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) v →
      G.oneMeetLevel (f u) (f v) =
        f ((finiteSupportGraph G (finiteLeafMeetSupport G L)).oneMeetLevel u v))
    (hTwo : ∀ a b c d : Nat,
      a < b → c < d →
      3 ≤ a → a < (finiteLeafMeetSupport G L).card →
      3 ≤ b → b < (finiteLeafMeetSupport G L).card →
      3 ≤ c → c < (finiteLeafMeetSupport G L).card →
      3 ≤ d → d < (finiteLeafMeetSupport G L).card →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) a →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) b →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) c →
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) d →
      G.twoMeetLevel (f a) (f b) (f c) (f d) =
        f ((finiteSupportGraph G (finiteLeafMeetSupport G L)).twoMeetLevel a b c d)) :
    _root_.ThreeUniformDiaries.Ordered3Graph.FiniteAuxEmbedding
      (finiteSupportGraph G (finiteLeafMeetSupport G L))
      G f (finiteLeafMeetSupport G L).card := by
  let S := finiteLeafMeetSupport G L
  have DA : FiniteRoleDiaryBlock (finiteSupportGraph G S) S.card :=
    finiteLeafMeetSupport_is_finiteDiary D hLeaves
  have P :=
    finiteLeafMeetSupport_totalMap_preembedding
      D L hLeaves f hf hIndex hOne hTwo
  have hInduced :
      ∀ a b c : Nat, a < b → b < c → c < S.card →
        (G.edge (f a) (f b) (f c) ↔
          (finiteSupportGraph G S).edge a b c) := by
    intro a b c hab hbc hcn
    exact finiteLeafMeetSupport_totalMap_induced
      (G := G) L f hIndex a b c hab hbc hcn
  exact P.toFiniteAuxEmbedding_of_induced DA D hInduced

end DiaryLeafPriority
end ThreeUniformDiaries
