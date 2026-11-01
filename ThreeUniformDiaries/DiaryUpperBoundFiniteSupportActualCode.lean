import ThreeUniformDiaries.DiaryUpperBoundSupportFiniteAuxAssembly
import ThreeUniformDiaries.DiaryUpperBoundSupportIndexTotal
import ThreeUniformDiaries.DiaryFiniteLeafMeetS2Reduct
import ThreeUniformDiaries.DiaryFinitePointedEnumNode

/-!
# Track A: unconditional genuine finite ATR code of any diary leaf-meet support

For every countable full RoleDiary D and every finite set L of
genuine leaves, the induced finite support S_L generated from L
is a genuine finite full diary. This file proves that the literal
increasing inclusion of S_L into the ambient D is not merely
type-respecting on leaves: it is a GENUINE FINITE
AUXILIARY-TYPE-RESPECTING embedding, including mixed split/leaf
tests at omitted target enumeration levels.

The proof combines:
1. exact S1/S2 selected-leaf numerical meet transport (merged Track B #988);
2. a global strict monotonisation of the finite support index (#996);
3. marker/role/induced support representation and complete finite
   leaf-preembedding to ATR conversion (Track A #998/#995/#993).

All assumptions are discharged from RoleDiary and the finite set L.
The resulting actual Fin m colour code has no infinite-source tail
data. In the two-meet case the first coordinate gives an explicit
bound on the capped meet, so all displayed finite indices are genuine.
No countable unavoidability or final diary Ramsey theorem is invoked.

The remaining upper-bound tasks are to identify a marked source
index for every labelled A-copy and count the possible genuine
marked diary shapes, then instantiate direct upper transfer #981.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

variable {G : Ordered3Graph Nat} {L : Finset Nat}

/-- Cap identity at a repeated singleton coordinate, with the
decidability of the finite maximal-agreement search explicit. -/
private theorem singletonMeet_self_at_nat
    (K : Ordered3Graph Nat) (x : Nat) :
    K.oneMeetLevel x x = x := by
  classical
  have hbound : K.oneMeetLevel x x ≤ x := by
    simpa only [min_self] using K.oneMeetLevel_le_min x x
  have hagree : K.SameOneTypeBelow x x x := by
    intro a b hab hb
    exact Iff.rfl
  have hge : x ≤ K.oneMeetLevel x x :=
    Nat.le_findGreatest (by simp) hagree
  exact Nat.le_antisymm hbound hge

/-- Complete one-meet transport under the ACTUAL total increasing
finite-support enumeration, for EVERY pair of selected leaves.
The diagonal is a cap; a reversed pair uses commutativity.
In particular no unjustified assumption that source leaves are
ordered by the given labels is made. -/
theorem finiteLeafMeetSupport_total_leaf_oneMeet
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (i j : Nat)
    (hi3 : 3 ≤ i) (hi : i < (finiteLeafMeetSupport G L).card)
    (hj3 : 3 ≤ j) (hj : j < (finiteLeafMeetSupport G L).card)
    (hiLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) i)
    (hjLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) j) :
    G.oneMeetLevel
      (finiteSupportIndexTotal (finiteLeafMeetSupport G L) i)
      (finiteSupportIndexTotal (finiteLeafMeetSupport G L) j) =
    finiteSupportIndexTotal (finiteLeafMeetSupport G L)
      ((finiteSupportGraph G (finiteLeafMeetSupport G L)).oneMeetLevel i j) := by
  classical
  let S := finiteLeafMeetSupport G L
  let H := finiteSupportGraph G S
  let f := finiteSupportIndexTotal S
  have hOrdered :
      ∀ u v : Nat,
        3 ≤ u → u < S.card → 3 ≤ v → v < S.card →
        IsLeaf H u → IsLeaf H v → u < v →
        G.oneMeetLevel (f u) (f v) = f (H.oneMeetLevel u v) := by
    intro u v hu3 hu hv3 hv huLeaf hvLeaf huv
    have hU : finiteSupportIndex S u ∈ L :=
      finiteLeafMeetSupport_reindexed_leaf_mem_L
        D hLeaves u hu3 hu huLeaf
    have hV : finiteSupportIndex S v ∈ L :=
      finiteLeafMeetSupport_reindexed_leaf_mem_L
        D hLeaves v hv3 hv hvLeaf
    have hExact :=
      (finiteLeafMeetSupport_selected_S1_exact_and_role
        D hLeaves u v hu hv huv hU hV).1
    have hm : H.oneMeetLevel u v < S.card := by
      have hBound := H.oneMeetLevel_le_min u v
      omega
    simpa only [
      f,
      finiteSupportIndexTotal_inside S u hu,
      finiteSupportIndexTotal_inside S v hv,
      finiteSupportIndexTotal_inside S (H.oneMeetLevel u v) hm
    ] using hExact
  rcases lt_trichotomy i j with hij | heq | hji
  · exact hOrdered i j hi3 hi hj3 hj hiLeaf hjLeaf hij
  · subst j
    change G.oneMeetLevel (f i) (f i) = f (H.oneMeetLevel i i)
    rw [singletonMeet_self_at_nat G (f i), singletonMeet_self_at_nat H i]
  · have hReverse := hOrdered j i hj3 hj hi3 hi hjLeaf hiLeaf hji
    change G.oneMeetLevel (f i) (f j) = f (H.oneMeetLevel i j)
    calc
      G.oneMeetLevel (f i) (f j) =
          G.oneMeetLevel (f j) (f i) :=
        finiteBlock_oneMeet_comm G (f i) (f j)
      _ = f (H.oneMeetLevel j i) := hReverse
      _ = f (H.oneMeetLevel i j) :=
        congrArg f (finiteBlock_oneMeet_comm H j i)

/-- Complete full ordered leaf-pair meet transport under the
ACTUAL total support index, including the S2 cap, marker 1, and
two-split cases. The source pair comparison is not required
to have distinct first members. -/
theorem finiteLeafMeetSupport_total_leaf_twoMeet
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (han : a < (finiteLeafMeetSupport G L).card)
    (hb3 : 3 ≤ b) (hbn : b < (finiteLeafMeetSupport G L).card)
    (hc3 : 3 ≤ c) (hcn : c < (finiteLeafMeetSupport G L).card)
    (hd3 : 3 ≤ d) (hdn : d < (finiteLeafMeetSupport G L).card)
    (haLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) a)
    (hbLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) b)
    (hcLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) c)
    (hdLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) d) :
    G.twoMeetLevel
      (finiteSupportIndexTotal (finiteLeafMeetSupport G L) a)
      (finiteSupportIndexTotal (finiteLeafMeetSupport G L) b)
      (finiteSupportIndexTotal (finiteLeafMeetSupport G L) c)
      (finiteSupportIndexTotal (finiteLeafMeetSupport G L) d) =
    finiteSupportIndexTotal (finiteLeafMeetSupport G L)
      ((finiteSupportGraph G (finiteLeafMeetSupport G L)).twoMeetLevel a b c d) := by
  let S := finiteLeafMeetSupport G L
  let H := finiteSupportGraph G S
  have hExact :=
    (finiteLeafMeetSupport_reindexed_S2_exact_and_role
      D hLeaves a b c d han hbn hcn hdn
      hab hcd haLeaf hbLeaf hcLeaf hdLeaf).1
  have hm : H.twoMeetLevel a b c d < S.card :=
    lt_of_le_of_lt
      (le_trans (H.twoMeetLevel_le_min a b c d)
        (min_le_left a c)) han
  change G.twoMeetLevel
      (finiteSupportIndexTotal S a)
      (finiteSupportIndexTotal S b)
      (finiteSupportIndexTotal S c)
      (finiteSupportIndexTotal S d) =
    finiteSupportIndexTotal S (H.twoMeetLevel a b c d)
  rw [finiteSupportIndexTotal_inside S a han,
    finiteSupportIndexTotal_inside S b hbn,
    finiteSupportIndexTotal_inside S c hcn,
    finiteSupportIndexTotal_inside S d hdn,
    finiteSupportIndexTotal_inside S (H.twoMeetLevel a b c d) hm]
  exact hExact

/-- No longer conditional: the induced finite support generated
by ANY finite leaf set of a genuine full countable diary embeds
into that diary with every actual auxiliary type reflected through
the full original enumeration. -/
theorem finiteLeafMeetSupport_unconditional_finiteAuxEmbedding
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u) :
    ThreeUniformDiaries.Ordered3Graph.FiniteAuxEmbedding
      (finiteSupportGraph G (finiteLeafMeetSupport G L))
      G
      (finiteSupportIndexTotal (finiteLeafMeetSupport G L))
      (finiteLeafMeetSupport G L).card := by
  let S := finiteLeafMeetSupport G L
  exact finiteLeafMeetSupport_totalMap_finiteAuxEmbedding
    D L hLeaves
    (finiteSupportIndexTotal S)
    (finiteSupportIndexTotal_strictMono S)
    (fun u hu => finiteSupportIndexTotal_inside S u hu)
    (fun u v hu3 hu hv3 hv huLeaf hvLeaf =>
      finiteLeafMeetSupport_total_leaf_oneMeet
        D hLeaves u v hu3 hu hv3 hv huLeaf hvLeaf)
    (fun a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
          haLeaf hbLeaf hcLeaf hdLeaf =>
      finiteLeafMeetSupport_total_leaf_twoMeet
        D hLeaves a b c d hab hcd
        ha3 han hb3 hbn hc3 hcn hd3 hdn
        haLeaf hbLeaf hcLeaf hdLeaf)

/-- A genuine FINITE auxiliary embedding image with precisely the
real source vertices. The abstract source is the first |S_L|
levels of the finite support hypergraph, represented by its
canonical finite EnumNode and zero-extended ONLY for typing.
No colouring can inspect any invented infinite tail. -/
noncomputable def finiteLeafMeetSupport_actualAuxCode
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u) :
    ThreeUniformDiaries.Ordered3Graph.FiniteAuxEmbeddingImage
      ((finiteSupportGraph G (finiteLeafMeetSupport G L)).initialSegment
        (finiteLeafMeetSupport G L).card).toOrdered3Graph
      G
      (finiteLeafMeetSupport G L).card := by
  let S := finiteLeafMeetSupport G L
  let f := finiteSupportIndexTotal S
  have hAux : ThreeUniformDiaries.Ordered3Graph.FiniteAuxEmbedding (finiteSupportGraph G S)
      G f S.card :=
    finiteLeafMeetSupport_unconditional_finiteAuxEmbedding
      D hLeaves
  exact ThreeUniformDiaries.Ordered3Graph.FiniteAuxEmbeddingImage.ofFiniteAuxEmbedding
    f hAux.of_initialSegment

end DiaryLeafPriority
end ThreeUniformDiaries
