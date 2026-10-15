import ThreeUniformDiaries.DiaryFusedOrientationPivot
import ThreeUniformDiaries.DiaryLexEarlierComplement
import ThreeUniformDiaries.DiaryOrientationUniformSign

/-!
# A finite calibration triple forces opposite increasing-pair orientations

The global 3-uniform lower-bound orientation problem needs one target
comparison connecting the positive and negative source diary
leaf-pair classes. A simple finite source configuration is enough:

Choose vertices m<a<b<c, with m the exact singleton meet of a,b,
and a,c having the same singleton type through m+1.
The verified earlier-meet orientation replacement shows that
LexEarlier(a,b) equals LexEarlier(c,b); swapping the latter pair
gives the complement of LexEarlier(b,c).

The same argument works AFTER an arbitrarily gappy
type-respecting embedding in the generic 3-hypergraph and the
genuinely UNORDERED outer hypergraph embedding: its fused image
is increasing and induced, the source first-disagreement
witness bounds the target meet, and gappy I2 transfers the
close singleton types. Thus the target orientations of the
two INCREASING pairs (a,b) and (b,c) are also opposite.

When a,b,c are diary leaves this immediately supplies one
cross-class opposite-sign orientation witness, independent of
which of the two ordered pairs carries the positive sign.
The remaining geometric question is to realize such a
calibration triple in a suitable diary/extension; no
unconditional existence is asserted here.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The minimal source configuration behind a three-leaf
orientation calibration. There are no hidden diary role or
universal embedding assumptions. -/
structure OrientationCalibrationTriple (H : Ordered3Graph Nat) where
  m : Nat
  a : Nat
  b : Nat
  c : Nat
  m_lt_a : m < a
  a_lt_b : a < b
  b_lt_c : b < c
  meet_ab : H.oneMeetLevel a b = m
  same_ac : H.SameOneTypeBelow (m+1) a c

namespace OrientationCalibrationTriple

open UnorderedEmbedding

/-- Both the source comparison and its actual target image
have opposite LexEarlier signs on the INCREASING ordered pairs
(a,b) and (b,c). The source need not be a diary. -/
theorem source_and_stabilised_target_opposite
    {H : Ordered3Graph Nat}
    (T : OrientationCalibrationTriple H)
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting) :
    (DiaryLeafPriority.LexEarlier H T.a T.b ↔
      ¬ DiaryLeafPriority.LexEarlier H T.b T.c) ∧
    (let φ := stabilisedSource G K F ψ
     DiaryLeafPriority.LexEarlier K (φ T.a) (φ T.b) ↔
      ¬ DiaryLeafPriority.LexEarlier K (φ T.b) (φ T.c)) := by
  let φ := stabilisedSource G K F ψ
  have hmb : T.m < T.b := lt_trans T.m_lt_a T.a_lt_b
  have hmc : T.m < T.c := lt_trans hmb T.b_lt_c
  have hmeetLe : H.oneMeetLevel T.a T.b ≤ T.m := by
    rw [T.meet_ab]
  have hSourcePivot :
      DiaryLeafPriority.LexEarlier H T.a T.b ↔
      DiaryLeafPriority.LexEarlier H T.c T.b :=
    H.lexEarlier_stable_under_close_one_types
      T.m T.a T.b T.c
      T.m_lt_a hmb hmc T.same_ac hmeetLe
  have hSourceSwap :
      DiaryLeafPriority.LexEarlier H T.c T.b ↔
      ¬ DiaryLeafPriority.LexEarlier H T.b T.c :=
    DiaryLeafPriority.lexEarlier_swap_complement
      H T.c T.b (ne_of_gt T.b_lt_c)
  have hTargetPivot :
      DiaryLeafPriority.LexEarlier K (φ T.a) (φ T.b) ↔
      DiaryLeafPriority.LexEarlier K (φ T.c) (φ T.b) :=
    UnorderedEmbedding.stabilisedSource_lexEarlier_pivot
      G K F ψ hψ T.m T.a T.b T.c
      T.m_lt_a hmb hmc T.meet_ab T.same_ac
  have hTargetSwap :
      DiaryLeafPriority.LexEarlier K (φ T.c) (φ T.b) ↔
      ¬ DiaryLeafPriority.LexEarlier K (φ T.b) (φ T.c) :=
    DiaryLeafPriority.lexEarlier_swap_complement
      K (φ T.c) (φ T.b)
      (ne_of_gt (φ.strictMono T.b_lt_c))
  exact ⟨hSourcePivot.trans hSourceSwap,
    hTargetPivot.trans hTargetSwap⟩

end OrientationCalibrationTriple
end Ordered3Graph

namespace DiaryLeafPriority

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

/-- When a calibration triple consists of actual diary leaves,
its two increasing leaf pairs give source orientation classes
of opposite sign and target orientations of opposite sign.
The positive pair is selected according to its genuine source
orientation, not by inventing a global orientation convention. -/
theorem calibrationTriple_exists_opposite_lex_anchor_pairs
    {H : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (T : OrientationCalibrationTriple H)
    (ha : IsLeaf H T.a)
    (hb : IsLeaf H T.b)
    (hc : IsLeaf H T.c) :
    ∃ p q : OrderedLeafPair H,
      LexEarlier H p.first p.second ∧
      ¬ LexEarlier H q.first q.second ∧
      (LexEarlier K (stabilisedSource G K F ψ p.first)
         (stabilisedSource G K F ψ p.second) ↔
       ¬ LexEarlier K (stabilisedSource G K F ψ q.first)
         (stabilisedSource G K F ψ q.second)) := by
  let p : OrderedLeafPair H :=
    ⟨T.a, T.b, T.a_lt_b, ha, hb⟩
  let q : OrderedLeafPair H :=
    ⟨T.b, T.c, T.b_lt_c, hb, hc⟩
  obtain ⟨hSource, hTarget⟩ :=
    T.source_and_stabilised_target_opposite G K F ψ hψ
  by_cases hPos : LexEarlier H T.a T.b
  · exact ⟨p, q, hPos, hSource.mp hPos, hTarget⟩
  · have hPosQ : LexEarlier H T.b T.c := by
      by_contra hNo
      exact hPos (hSource.mpr hNo)
    have hOppReversed :
        LexEarlier K (stabilisedSource G K F ψ T.b)
          (stabilisedSource G K F ψ T.c) ↔
        ¬ LexEarlier K (stabilisedSource G K F ψ T.a)
          (stabilisedSource G K F ψ T.b) := by
      classical
      by_cases hp : LexEarlier K (stabilisedSource G K F ψ T.a)
          (stabilisedSource G K F ψ T.b) <;>
      by_cases hq : LexEarlier K (stabilisedSource G K F ψ T.b)
          (stabilisedSource G K F ψ T.c) <;> simp_all
    exact ⟨q, p, hPosQ, hPos, hOppReversed⟩

end DiaryLeafPriority
end ThreeUniformDiaries
