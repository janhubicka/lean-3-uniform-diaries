import ThreeUniformDiaries.DiaryNativeOppositeAmalgam
import ThreeUniformDiaries.DiaryFourTailCalibration
import ThreeUniformDiaries.DiaryOneSplitNextCut

/-!
# Opposite diary orientation classes actually yield a calibration triple

For a positive pair of diary leaves a<b and a negative pair c<d,
take their two canonical three-tail native pointed source pictures,
compressing the whole generic prefix j=ψ(3).

The verified V/E/S compatibility identifies the split and positive
central leaf profiles, so these pictures admit the actual ordered
four-tail free amalgam C. Its extra leaves appear as

  j+1 negative (from a), j+2 positive (from b/c),
  j+3 negative (from d).

The one-split V/E witness forces the FIRST pair's singleton meet
at the shared split j. The two negative branches have equal full
pair profiles through the entire generic prefix j, including
the edge bits at their respective one-split vertices. Hence
their amalgamated versions have equal singleton types through
the successor cut j+1.

This gives a genuine OrientationCalibrationTriple in C:
the three increasing exterior leaves, with singleton meet j
and equal negative singleton types through j+1.

Crucially the first disagreement may be witnessed at ψ(0),
which is below j but need not equal vertex 0. The proof uses
the FULL gappy type-respecting source map and assumes neither
ψ(0)=0 nor target-level convexity.

This constructs the FINITE SOURCE calibration. The remaining
proof must embed C into G fixing prefix j and construct two
finite ATR codes comparing the source diary pairs to its
calibration pairs. It does not claim global orientation yet.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {H : Ordered3Graph Nat}

/-- The actual positive/negative diary three-tail source
amalgam contains a fully specified orientation calibration
triple. No calibration data or mixed-type gap preservation
is supplied by the caller. -/
noncomputable def oppositeLex_native_fourTail_has_calibrationTriple
    (D : RoleDiary H)
    (G : GenericEnumerated3Graph)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hplus : LexEarlier H a b)
    (hminus : ¬ LexEarlier H c d) :
    let j := ψ 3
    let m := H.oneMeetLevel a b
    let n := H.oneMeetLevel c d
    let A := G.graph.pullback
      (threeTailInsertion j (ψ m) (ψ a) (ψ b))
    let B := G.graph.pullback
      (threeTailInsertion j (ψ n) (ψ c) (ψ d))
    OrientationCalibrationTriple (threeTailFreeAmalgam A B j) := by
  classical
  let j := ψ 3
  let m := H.oneMeetLevel a b
  let n := H.oneMeetLevel c d
  let fPlus := threeTailInsertion j (ψ m) (ψ a) (ψ b)
  let fMinus := threeTailInsertion j (ψ n) (ψ c) (ψ d)
  let A := G.graph.pullback fPlus
  let B := G.graph.pullback fMinus
  have hOverlap : ThreeTailOverlapCompatible A B j :=
    D.oppositeLex_native_threeTail_overlap
      G ψ hψ a b c d hab hcd ha hb hc hd hplus hminus
  have hm : IsOneSplit H m :=
    D.singleton_meets a b ha hb (ne_of_lt hab)
  have hma : m < a :=
    D.leaf_meet_lt_first a b ha hb (ne_of_lt hab)
  have hmb : m < b := lt_trans hma hab
  have ha3 : 3 ≤ a := ha.1
  have hb3 : 3 ≤ b := hb.1
  have hSourceSame : H.SameOneTypeBelow 3 a b := by
    intro x y hxy hy
    exact (H.oneMeetLevel_agree a b) hxy
      (lt_of_lt_of_le hy hm.1)
  have hGenericSame : G.graph.SameOneTypeBelow j (ψ a) (ψ b) :=
    (hψ.one 3 a b ha3 hb3).mp hSourceSame
  have hSame : A.SameOneTypeBelow j (j+1) (j+2) := by
    intro x y hxy hy
    have hx : x < j := by omega
    change G.graph.edge (fPlus x) (fPlus y) (fPlus (j+1)) ↔
      G.graph.edge (fPlus x) (fPlus y) (fPlus (j+2))
    simpa only [fPlus,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) x hx,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) y hy,
      threeTailInsertion_first j (ψ m) (ψ a) (ψ b),
      threeTailInsertion_second j (ψ m) (ψ a) (ψ b)] using
        hGenericSame hxy hy
  have hSourceDiff : ¬ (H.edge 0 m a ↔ H.edge 0 m b) :=
    D.oneSplit_witness_opposite_marker
      m a b hm ha hb hma hmb rfl
  have h0m : 0 < m := by have h := hm.1; omega
  have hGenericDiff :
      ¬ (G.graph.edge (ψ 0) (ψ m) (ψ a) ↔
         G.graph.edge (ψ 0) (ψ m) (ψ b)) := by
    intro heq
    have hA : H.edge 0 m a ↔
        G.graph.edge (ψ 0) (ψ m) (ψ a) :=
      ψ.edge_iff h0m hma
    have hB : H.edge 0 m b ↔
        G.graph.edge (ψ 0) (ψ m) (ψ b) :=
      ψ.edge_iff h0m hmb
    exact hSourceDiff (hA.trans (heq.trans hB.symm))
  have h0j : ψ 0 < j :=
    ψ.strictMono (by omega)
  have hSplit :
      ∃ z, z < j ∧
        ¬ (A.edge z j (j+1) ↔ A.edge z j (j+2)) := by
    refine ⟨ψ 0, h0j, ?_⟩
    change
      ¬ (G.graph.edge (fPlus (ψ 0)) (fPlus j) (fPlus (j+1)) ↔
         G.graph.edge (fPlus (ψ 0)) (fPlus j) (fPlus (j+2)))
    simpa only [fPlus,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) (ψ 0) h0j,
      threeTailInsertion_split j (ψ m) (ψ a) (ψ b),
      threeTailInsertion_first j (ψ m) (ψ a) (ψ b),
      threeTailInsertion_second j (ψ m) (ψ a) (ψ b)] using
        hGenericDiff
  have hNeg : G.graph.SameTwoTypeBelow j
      (ψ m) (ψ a) (ψ n) (ψ d) :=
    (D.oppositeLex_same_branch_profiles_in_generic
      G ψ hψ a b c d hab hcd ha hb hc hd hplus hminus).2
  have hNegOne : G.graph.SameOneTypeBelow j (ψ a) (ψ d) :=
    hNeg.2.1
  have hNegAux : G.graph.SameAuxTypeBelow j
      (ψ m) (ψ a) (ψ n) (ψ d) := hNeg.2.2
  have hNegativePrefix :
      ∀ x y, x < y → y < j →
        (A.edge x y (j+1) ↔ B.edge x y (j+2)) := by
    intro x y hxy hy
    have hx : x < j := by omega
    change G.graph.edge (fPlus x) (fPlus y) (fPlus (j+1)) ↔
      G.graph.edge (fMinus x) (fMinus y) (fMinus (j+2))
    simpa only [fPlus, fMinus,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) x hx,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) y hy,
      threeTailInsertion_fix_prefix j (ψ n) (ψ c) (ψ d) x hx,
      threeTailInsertion_fix_prefix j (ψ n) (ψ c) (ψ d) y hy,
      threeTailInsertion_first j (ψ m) (ψ a) (ψ b),
      threeTailInsertion_second j (ψ n) (ψ c) (ψ d)] using
        hNegOne hxy hy
  have hNegativeSplit :
      ∀ x, x < j →
        (A.edge x j (j+1) ↔ B.edge x j (j+2)) := by
    intro x hx
    change G.graph.edge (fPlus x) (fPlus j) (fPlus (j+1)) ↔
      G.graph.edge (fMinus x) (fMinus j) (fMinus (j+2))
    simpa only [fPlus, fMinus,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) x hx,
      threeTailInsertion_fix_prefix j (ψ n) (ψ c) (ψ d) x hx,
      threeTailInsertion_split j (ψ m) (ψ a) (ψ b),
      threeTailInsertion_split j (ψ n) (ψ c) (ψ d),
      threeTailInsertion_first j (ψ m) (ψ a) (ψ b),
      threeTailInsertion_second j (ψ n) (ψ c) (ψ d)] using
        (hNegAux (a := x) hx)
  exact threeTailFreeAmalgam_calibrationTriple
    A B j hOverlap hSame hSplit hNegativePrefix hNegativeSplit

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
