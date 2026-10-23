import ThreeUniformDiaries.DiaryFiniteSignRootedRawTerminalSupport

/-!
# Exact source type agreement in the sign-rooted raw amalgam

The raw sign-rooted union has many off-path vertices at levels
preceding a given terminal. Its terminal-locality theorem shows
that every raw edge with an off-path earlier vertex is FALSE.
Consequently each original source branch preserves not only its
induced ternary relation but also the equality relation on
singleton, auxiliary, and complete ordered-pair types at every
SOURCE-LEVEL cut.

The tests in this file quantify over ALL sign-rooted raw nodes
whose original first-coordinate levels lie below the cut,
including nodes belonging only to other branches. This is
strictly stronger than just inducedness of each branch.

It does NOT assert equality of mixed numerical meets after
arbitrary linearly ordering/reindexing all raw nodes, nor does
it cover the additional cross-branch Devlin edges necessary
for V3. It is a precise raw-data input for those later steps.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- Raw singleton type equality at a SOURCE LEVEL l, testing
every earlier pair of actual sign-rooted raw nodes. -/
def RawSameOneTypeBelow
    (F : FiniteSignRootedFlipFamily A n ι)
    (l : Nat) (U V : FiniteSignRootedNode A n) : Prop :=
  ∀ X Y : FiniteSignRootedNode A n,
    X.1 < Y.1 → Y.1 < l →
      ((F.rawAmalgam).edge X Y U ↔
       (F.rawAmalgam).edge X Y V)

/-- Every source singleton-type equality below l survives
all earlier off-branch raw tests, and conversely the raw
predicate reflects every actual source test on the branch. -/
theorem rawSameOneTypeBelow_iff_source
    (F : FiniteSignRootedFlipFamily A n ι)
    (i : ι) (l u v : Nat)
    (hlu : l ≤ u) (hlv : l ≤ v)
    (hun : u < n) (hvn : v < n) :
    F.RawSameOneTypeBelow l (F.node i u) (F.node i v) ↔
      (F.graph i).SameOneTypeBelow l u v := by
  constructor
  · intro hRaw x y hxy hyl
    have hNodeXY :
        (F.node i x).1 < (F.node i y).1 := by
      simpa only [node_level] using hxy
    have hNodeYl : (F.node i y).1 < l := by
      simpa only [node_level] using hyl
    have hBits :=
      hRaw (F.node i x) (F.node i y) hNodeXY hNodeYl
    have hxyu : y < u := by omega
    have hxyv : y < v := by omega
    exact ((F.rawAmalgam_edge_iff i x y u hxy hxyu hun).symm).trans
      (hBits.trans (F.rawAmalgam_edge_iff i x y v hxy hxyv hvn))
  · intro hSource X Y hXY hYl
    by_cases hX : X = F.node i X.1
    · by_cases hY : Y = F.node i Y.1
      · have hXYu : Y.1 < u := by omega
        have hXYv : Y.1 < v := by omega
        have hU :
            (F.rawAmalgam).edge X Y (F.node i u) ↔
              (F.graph i).edge X.1 Y.1 u := by
          rw [hX,hY]
          exact F.rawAmalgam_edge_iff i X.1 Y.1 u
            hXY hXYu hun
        have hV :
            (F.rawAmalgam).edge X Y (F.node i v) ↔
              (F.graph i).edge X.1 Y.1 v := by
          rw [hX,hY]
          exact F.rawAmalgam_edge_iff i X.1 Y.1 v
            hXY hXYv hvn
        exact hU.trans ((hSource hXY hYl).trans hV.symm)
      · exact iff_of_false
          (F.rawAmalgam_no_offpath_edge_at_terminal i X Y u
            (Or.inr hY))
          (F.rawAmalgam_no_offpath_edge_at_terminal i X Y v
            (Or.inr hY))
    · exact iff_of_false
        (F.rawAmalgam_no_offpath_edge_at_terminal i X Y u
          (Or.inl hX))
        (F.rawAmalgam_no_offpath_edge_at_terminal i X Y v
          (Or.inl hX))

/-- Auxiliary ordered-pair type equality at a SOURCE LEVEL l
quantifies over every earlier raw node, including off-path
vertices, not just a selected source branch. -/
def RawSameAuxTypeBelow
    (F : FiniteSignRootedFlipFamily A n ι)
    (l : Nat)
    (U V U' V' : FiniteSignRootedNode A n) : Prop :=
  ∀ X : FiniteSignRootedNode A n, X.1 < l →
    ((F.rawAmalgam).edge X U V ↔
     (F.rawAmalgam).edge X U' V')

/-- Raw auxiliary tests have exactly the same equality
relations as the corresponding source ordered leaf-pair
tests, because every off-branch earlier test is absent. -/
theorem rawSameAuxTypeBelow_iff_source
    (F : FiniteSignRootedFlipFamily A n ι)
    (i : ι) (l u v w z : Nat)
    (hlu : l ≤ u) (hlw : l ≤ w)
    (huv : u < v) (hwz : w < z)
    (hvn : v < n) (hzn : z < n) :
    F.RawSameAuxTypeBelow l
      (F.node i u) (F.node i v)
      (F.node i w) (F.node i z) ↔
      (F.graph i).SameAuxTypeBelow l u v w z := by
  constructor
  · intro hRaw x hxl
    have hNodeX : (F.node i x).1 < l := by
      simpa only [node_level] using hxl
    have hRawTest := hRaw (F.node i x) hNodeX
    have hxu : x < u := by omega
    have hxw : x < w := by omega
    exact ((F.rawAmalgam_edge_iff i x u v hxu huv hvn).symm).trans
      (hRawTest.trans (F.rawAmalgam_edge_iff i x w z hxw hwz hzn))
  · intro hSource X hXl
    by_cases hOn : X = F.node i X.1
    · have hXU : X.1 < u := by omega
      have hXW : X.1 < w := by omega
      have hTestU :
          (F.rawAmalgam).edge X (F.node i u) (F.node i v) ↔
            (F.graph i).edge X.1 u v := by
        rw [hOn]
        exact F.rawAmalgam_edge_iff i X.1 u v hXU huv hvn
      have hTestW :
          (F.rawAmalgam).edge X (F.node i w) (F.node i z) ↔
            (F.graph i).edge X.1 w z := by
        rw [hOn]
        exact F.rawAmalgam_edge_iff i X.1 w z hXW hwz hzn
      exact hTestU.trans ((hSource hXl).trans hTestW.symm)
    · exact iff_of_false
        (F.rawAmalgam_no_offpath_edge_at_terminal i
          X (F.node i u) v (Or.inl hOn))
        (F.rawAmalgam_no_offpath_edge_at_terminal i
          X (F.node i w) z (Or.inl hOn))

/-- Exact full predecessor pair-type agreement in the raw
amalgam is precisely source full two-type agreement. Both
coordinate singleton types and the auxiliary pair type
are included; no false cross-branch meet assertion is made. -/
def RawSameTwoTypeBelow
    (F : FiniteSignRootedFlipFamily A n ι)
    (l : Nat)
    (U V U' V' : FiniteSignRootedNode A n) : Prop :=
  F.RawSameOneTypeBelow l U U' ∧
  F.RawSameOneTypeBelow l V V' ∧
  F.RawSameAuxTypeBelow l U V U' V'

theorem rawSameTwoTypeBelow_iff_source
    (F : FiniteSignRootedFlipFamily A n ι)
    (i : ι) (l a b c d : Nat)
    (hla : l ≤ a) (hlc : l ≤ c)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n) :
    F.RawSameTwoTypeBelow l
      (F.node i a) (F.node i b)
      (F.node i c) (F.node i d) ↔
        (F.graph i).SameTwoTypeBelow l a b c d := by
  have han : a < n := by omega
  have hcn : c < n := by omega
  change
    (F.RawSameOneTypeBelow l (F.node i a) (F.node i c) ∧
     F.RawSameOneTypeBelow l (F.node i b) (F.node i d) ∧
     F.RawSameAuxTypeBelow l
       (F.node i a) (F.node i b)
       (F.node i c) (F.node i d)) ↔
    ((F.graph i).SameOneTypeBelow l a c ∧
     (F.graph i).SameOneTypeBelow l b d ∧
     (F.graph i).SameAuxTypeBelow l a b c d)
  rw [F.rawSameOneTypeBelow_iff_source i l a c hla hlc han hcn,
      F.rawSameOneTypeBelow_iff_source i l b d
        (by omega) (by omega) hbn hdn,
      F.rawSameAuxTypeBelow_iff_source i l a b c d
        hla hlc hab hcd hbn hdn]

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
