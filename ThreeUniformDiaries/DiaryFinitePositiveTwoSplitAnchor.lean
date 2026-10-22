import ThreeUniformDiaries.DiaryFiniteLeafMeetTwoSplitDisagreement
import ThreeUniformDiaries.DiaryFiniteFlipTargetTransport
import ThreeUniformDiaries.DiaryFiniteLeafPreembeddingComposition

/-!
# One positive pair controls an entire E3 two-split column

In an actual finite pre-diary, all ordered leaf pairs positively
incident with a genuine two-split s have the SAME full pair type
through cut s+1. For a chosen positive pair (a,b), incidence
at s of every other ordered pair (u,v) is therefore equivalent
to s < twoMeetLevel(a,b,u,v).

The forward direction uses finite V2 coherence through s,
the E1--E5 exclusion of singleton tests with middle vertex s,
and the positive E3 bit. The reverse direction follows directly
from full pair-type agreement through the meet cut.

If a FINITE LEAF PREEMBEDDING f preserves full leaf pair meets,
role markers and a SINGLE positive E3 anchor bit for the chosen
pair (a,b), the same formula transports ALL E3 bits incident
with the source two-split s to its target image f(s).

This supplies a reusable finite 2-type control lemma for
future 2-split flip-absorber geometry. There is no assumption
that different split controls are independent. It neither
constructs a target nor asserts the general flip property.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- V2 coherence plus the genuine split's unique new E3 test
turns two positive pairs into full pair-type agreement at s+1. -/
theorem finite_twoSplit_positive_pairs_agree_next
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRolePrediaryBlock H n)
    (s a b u v : Nat)
    (hs : IsTwoSplit H s)
    (hab : a < b) (huv : u < v)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hPosAB : H.edge s a b)
    (hPosUV : H.edge s u v) :
    H.SameTwoTypeBelow (s+1) a b u v := by
  have hBelow : H.SameTwoTypeBelow s a b u v :=
    D.two_split_coherent s a b u v hs hab huv
      ha hb hu hv hPosAB hPosUV
  refine ⟨?_,?_,?_⟩
  · intro x y hxy hy
    by_cases hys : y < s
    · exact hBelow.1 hxy hys
    · have hyEq : y = s := by omega
      subst y
      exact iff_of_false
        (E_twoSplit_no_incoming_middle D.permitted_edge s x a hs)
        (E_twoSplit_no_incoming_middle D.permitted_edge s x u hs)
  · intro x y hxy hy
    by_cases hys : y < s
    · exact hBelow.2.1 hxy hys
    · have hyEq : y = s := by omega
      subst y
      exact iff_of_false
        (E_twoSplit_no_incoming_middle D.permitted_edge s x b hs)
        (E_twoSplit_no_incoming_middle D.permitted_edge s x v hs)
  · intro x hx
    by_cases hxs : x < s
    · exact hBelow.2.2 hxs
    · have hxEq : x = s := by omega
      subst x
      exact iff_of_true hPosAB hPosUV

/-- A single positive ordered leaf pair (a,b) at a genuine
two-split s exactly determines every other E3 incidence
at that split, by its COMPLETE pair-type meet with (a,b). -/
theorem finite_positive_twoSplit_edge_iff_later_twoMeet
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRolePrediaryBlock H n)
    (s a b u v : Nat)
    (hs : IsTwoSplit H s)
    (hab : a < b) (huv : u < v)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hsa : s < a) (hsu : s < u)
    (hPositive : H.edge s a b) :
    H.edge s u v ↔ s < H.twoMeetLevel a b u v := by
  classical
  constructor
  · intro hPositiveUV
    have hNext := finite_twoSplit_positive_pairs_agree_next
      D s a b u v hs hab huv ha hb hu hv hPositive hPositiveUV
    have hBound : s+1 ≤ min a u := by omega
    have hMeet : s+1 ≤ H.twoMeetLevel a b u v :=
      Nat.le_findGreatest hBound hNext
    omega
  · intro hLater
    have hSame : H.edge s a b ↔ H.edge s u v :=
      (H.twoMeetLevel_agree a b u v).2.2 hLater
    exact hSame.mp hPositive

/-- Under a genuine finite leaf preembedding, preserving ONE
positive E3 anchor at a source two-split forces preservation
of EVERY E3 edge and nonedge over that split.

No inducedness of the rest of the source is assumed; the key
input is exact full pair-type meet transport for all leaves. -/
theorem finite_leafPreembedding_twoSplit_E3_of_positive_anchor
    {A B : Ordered3Graph Nat} {n k : Nat}
    {f : Nat → Nat}
    (DA : FiniteRolePrediaryBlock A n)
    (DB : FiniteRolePrediaryBlock B k)
    (Q : FiniteLeafPreembedding A B n k f)
    (s a b : Nat)
    (hs : IsTwoSplit A s)
    (hab : a < b)
    (hsa : s < a)
    (hbn : b < n)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hPositiveA : A.edge s a b)
    (hPositiveB : B.edge (f s) (f a) (f b)) :
    ∀ u v : Nat, u < v → v < n →
      IsLeaf A u → IsLeaf A v → s < u →
      (A.edge s u v ↔ B.edge (f s) (f u) (f v)) := by
  intro u v huv hvn hu hv hsu
  have hsn : s < n := by omega
  have han : a < n := by omega
  have hun : u < n := by omega
  have hBs : IsTwoSplit B (f s) :=
    ((Q.role_iff s hs.1 hsn).2.2).mpr hs
  have hBa : IsLeaf B (f a) :=
    ((Q.role_iff a ha.1 han).1).mpr ha
  have hBb : IsLeaf B (f b) :=
    ((Q.role_iff b hb.1 hbn).1).mpr hb
  have hBu : IsLeaf B (f u) :=
    ((Q.role_iff u hu.1 hun).1).mpr hu
  have hBv : IsLeaf B (f v) :=
    ((Q.role_iff v hv.1 hvn).1).mpr hv
  have hSource :=
    finite_positive_twoSplit_edge_iff_later_twoMeet
      DA s a b u v hs hab huv ha hb hu hv hsa hsu hPositiveA
  have hTarget :=
    finite_positive_twoSplit_edge_iff_later_twoMeet
      DB (f s) (f a) (f b) (f u) (f v)
      hBs (Q.strictMono hab) (Q.strictMono huv)
      hBa hBb hBu hBv
      (Q.strictMono hsa) (Q.strictMono hsu) hPositiveB
  have hMeet :
      B.twoMeetLevel (f a) (f b) (f u) (f v) =
        f (A.twoMeetLevel a b u v) :=
    Q.leaf_twoMeet a b u v hab huv
      ha.1 han hb.1 hbn hu.1 hun hv.1 hvn ha hb hu hv
  have hOrder :
      s < A.twoMeetLevel a b u v ↔
        f s < f (A.twoMeetLevel a b u v) := by
    constructor
    · intro h
      exact Q.strictMono h
    · intro h
      by_contra hNot
      have hLe : A.twoMeetLevel a b u v ≤ s := Nat.le_of_not_gt hNot
      have hFLe := Q.strictMono.monotone hLe
      omega
  calc
    A.edge s u v ↔ s < A.twoMeetLevel a b u v := hSource
    _ ↔ f s < f (A.twoMeetLevel a b u v) := hOrder
    _ ↔ f s < B.twoMeetLevel (f a) (f b) (f u) (f v) := by rw [hMeet]
    _ ↔ B.edge (f s) (f u) (f v) := hTarget.symm

end DiaryLeafPriority
end ThreeUniformDiaries
