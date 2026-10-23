import ThreeUniformDiaries.DiaryFiniteFaithfulFlipSignature
import ThreeUniformDiaries.DiaryFiniteCanonicalSourceFlipOrbit

/-!
# A fixed, source-based finite flip signature and its cardinal bound

For each genuine two-split s, select ONCE a genuine source S2
pair-of-pairs witness (a,b),(c,d) with full two-type meet s.
For a chosen reference ordered leaf pair r<t, the signature of a
genuine flip T consists of:
 * the marker-one bit edge_T(1,r,t);
 * for each genuine source two-split s, the E3 bit edge_T(s,a_s,b_s).

The witness selection is independent of T. Equality of these fixed
bits forces literal equality of finite flip graphs, using the
previously verified global E2 rigidity and S2 witness E3 rigidity.
The set of realised signatures is a CONSTRAINED subset of a finite
Boolean cube; this file never asserts independent realisability.

The canonical edge-code orbit excludes discarded non-increasing
triple bits. Its injection into the signature space yields a
formal finite-cardinality bound (under an explicit reference pair),
not just an informal counting argument.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The finite index set of actual two-split vertices of a given
source diary. Its cardinal is the number of genuine two-splits
inside the bounded frame. -/
abbrev FiniteTwoSplitIndex (A : Ordered3Graph Nat) (n : Nat) :=
  {s : Fin n // IsTwoSplit A s.val}

/-- The finite number of actual two-splits, with decidability
chosen locally rather than required in theorem statements. -/
noncomputable def finiteTwoSplitCount
    (A : Ordered3Graph Nat) (n : Nat) : Nat := by
  classical
  exact Fintype.card (FiniteTwoSplitIndex A n)

/-- A genuine full-pair-meet witness for a given source two-split. -/
structure FiniteSelectedS2Witness
    (A : Ordered3Graph Nat) (n s : Nat) where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  hab : a < b
  hcd : c < d
  hbn : b < n
  hdn : d < n
  ha : IsLeaf A a
  hb : IsLeaf A b
  hc : IsLeaf A c
  hd : IsLeaf A d
  hsa : s < a
  hsc : s < c
  hMeet : A.twoMeetLevel a b c d = s

/-- The witness is selected ONCE from the source diary.
Neither a target flip nor its E3 edge bits are inputs. -/
noncomputable def finiteSelectedS2Witness
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (s : FiniteTwoSplitIndex A n) :
    FiniteSelectedS2Witness A n s.val.val := by
  obtain ⟨a,b,c,d,hab,hcd,_han,hbn,_hcn,hdn,
    ha,hb,hc,hd,hsa,hsc,hMeet⟩ :=
    DA.prediary.two_split_witness s.val.val
      s.property s.val.isLt
  exact ⟨a,b,c,d,hab,hcd,hbn,hdn,
    ha,hb,hc,hd,hsa,hsc,hMeet⟩

/-- Fixed signature of any graph on the source frame, using
one selected marker-one reference pair and the source's
chosen S2 witnesses. Only the restriction to genuine flips
will be shown injective. -/
noncomputable def finiteFixedFlipSignature
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (r t : Nat) (T : Ordered3Graph Nat) :
    Bool × (FiniteTwoSplitIndex A n → Bool) := by
  classical
  exact (decide (T.edge 1 r t),
    fun s => decide (T.edge s.val.val
      (finiteSelectedS2Witness DA s).a
      (finiteSelectedS2Witness DA s).b))

/-- Two actual source flips with the same FIXED signature
are the same finite ordered hypergraph, including all
edges and nonedges. -/
theorem finiteFixedFlipSignature_injective_on_flips
    {A B C : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (r t : Nat) (hrt : r < t) (htn : t < n)
    (hr : IsLeaf A r) (ht : IsLeaf A t)
    (FB : FiniteDiaryFlip A B n)
    (FC : FiniteDiaryFlip A C n)
    (hEqual : finiteFixedFlipSignature DA r t B =
      finiteFixedFlipSignature DA r t C) :
    B = C := by
  classical
  have hMarkerDec :
      decide (B.edge 1 r t) = decide (C.edge 1 r t) := by
    have h := congrArg
      (fun z : Bool × (FiniteTwoSplitIndex A n → Bool) => z.1)
      hEqual
    simpa only [finiteFixedFlipSignature] using h
  have hMarker : B.edge 1 r t ↔ C.edge 1 r t := by
    by_cases hB : B.edge 1 r t <;>
      by_cases hC : C.edge 1 r t <;> simp_all
  have hS2 :
      ∀ s : Nat, IsTwoSplit A s →
        ∃ a b c d : Nat,
          a < b ∧ c < d ∧ b < n ∧ d < n ∧
          IsLeaf A a ∧ IsLeaf A b ∧
          IsLeaf A c ∧ IsLeaf A d ∧
          s < a ∧ s < c ∧
          A.twoMeetLevel a b c d = s ∧
          (B.edge s a b ↔ C.edge s a b) := by
    intro s hs
    let i : FiniteTwoSplitIndex A n :=
      ⟨⟨s,DA.prediary.twoSplit_lt s hs⟩,hs⟩
    let W := finiteSelectedS2Witness DA i
    have hDec :
        decide (B.edge s W.a W.b) =
          decide (C.edge s W.a W.b) := by
      have h := congrArg
        (fun z : Bool × (FiniteTwoSplitIndex A n → Bool) => z.2 i)
        hEqual
      change decide (B.edge s W.a W.b) =
        decide (C.edge s W.a W.b) at h
      exact h
    have hBit : B.edge s W.a W.b ↔ C.edge s W.a W.b := by
      by_cases hB : B.edge s W.a W.b <;>
        by_cases hC : C.edge s W.a W.b <;> simp_all
    exact ⟨W.a,W.b,W.c,W.d,W.hab,W.hcd,
      W.hbn,W.hdn,W.ha,W.hb,W.hc,W.hd,
      W.hsa,W.hsc,W.hMeet,hBit⟩
  exact finite_two_flips_eq_of_global_marker_and_S2_bits
    FB FC r t hrt htn hr ht hMarker hS2

/-- Restrict the fixed signature to a member of the canonical
finite source-flip orbit; redundant raw Boolean tables are
excluded before invoking the injection theorem. -/
noncomputable def finiteCanonicalFlipSignature
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (r t : Nat) (code : FiniteDiaryEdgeCode n) :
    Bool × (FiniteTwoSplitIndex A n → Bool) :=
  finiteFixedFlipSignature DA r t (finiteDiaryCodeGraph n code)

/-- The fixed signature injects the COMPLETE CANONICAL
source-flip orbit into its finite signature space. -/
theorem finiteCanonicalFlipSignature_injOn
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (r t : Nat) (hrt : r < t) (htn : t < n)
    (hr : IsLeaf A r) (ht : IsLeaf A t)
    (x y : FiniteDiaryEdgeCode n)
    (hx : x ∈ finiteCanonicalSourceFlipCodes A n)
    (hy : y ∈ finiteCanonicalSourceFlipCodes A n)
    (hEq : finiteCanonicalFlipSignature DA r t x =
      finiteCanonicalFlipSignature DA r t y) :
    x = y := by
  have Fx : FiniteDiaryFlip A (finiteDiaryCodeGraph n x) n :=
    (mem_finiteSourceFlipCodes_iff A n x).mp
      ((mem_finiteCanonicalSourceFlipCodes_iff A n x).mp hx).1
  have Fy : FiniteDiaryFlip A (finiteDiaryCodeGraph n y) n :=
    (mem_finiteSourceFlipCodes_iff A n y).mp
      ((mem_finiteCanonicalSourceFlipCodes_iff A n y).mp hy).1
  apply finiteCanonicalSourceFlipCodes_decode_injective
    A n x y hx hy
  exact finiteFixedFlipSignature_injective_on_flips
    DA r t hrt htn hr ht Fx Fy hEq

/-- The cardinality of the realised finite canonical orbit
is bounded by the Boolean signature space, counting ONE
marker bit and ONE bit per genuine two-split. This is a
formal injectivity-and-finite-counting conclusion. -/
theorem finiteCanonicalFlipSignature_card_bound
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (r t : Nat) (hrt : r < t) (htn : t < n)
    (hr : IsLeaf A r) (ht : IsLeaf A t) :
    Fintype.card
      {x : FiniteDiaryEdgeCode n //
        x ∈ finiteCanonicalSourceFlipCodes A n} ≤
      2 ^ (finiteTwoSplitCount A n + 1) := by
  classical
  let Orbit :=
    {x : FiniteDiaryEdgeCode n //
      x ∈ finiteCanonicalSourceFlipCodes A n}
  let Signature := Bool × (FiniteTwoSplitIndex A n → Bool)
  let code : Orbit → Signature :=
    fun x => finiteCanonicalFlipSignature DA r t x.val
  have hInjective : Function.Injective code := by
    intro x y h
    apply Subtype.ext
    exact finiteCanonicalFlipSignature_injOn
      DA r t hrt htn hr ht x.val y.val
      x.property y.property h
  have hBound : Fintype.card Orbit ≤ Fintype.card Signature :=
    Fintype.card_le_of_injective code hInjective
  have hSize :
      Fintype.card Signature =
        2 ^ (finiteTwoSplitCount A n + 1) := by
    dsimp [Signature, finiteTwoSplitCount]
    simp [Fintype.card_prod, pow_succ, mul_comm]
  simpa only [hSize] using hBound

end DiaryLeafPriority
end ThreeUniformDiaries
