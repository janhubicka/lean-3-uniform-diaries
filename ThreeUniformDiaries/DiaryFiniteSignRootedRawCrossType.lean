import ThreeUniformDiaries.DiaryFiniteSignRootedRawTypePreservation
import ThreeUniformDiaries.DiaryFiniteSignRootedVTwoParentCompatibility

/-!
# Cross-branch raw predecessor-type transport at a shared sign-rooted cut

The earlier raw type comparison is within one source branch.
Here we compare genuinely DIFFERENT branches whose sign-rooted
nodes are identified at a shared source cut s.

At every earlier source level k<s, the branches' nodes coincide
by prefix consistency. For an earlier raw vertex not on this
common prefix, ALL edges ending on either compared branch are
absent by exact raw terminal locality. Consequently equality of
the corresponding SOURCE Boolean one/auxiliary/pair codes below s
implies equality of their predecessor raw type tests even when
the earlier tests range over ALL nodes of the raw union.

The proof has NO hypotheses on the orientations of E3 at the
current cut s; these are allowed to differ. The subsequent
application to V2-positive pairs will use the already verified
cross-flip S2 parent-profile theorem.

The result is about the RAW union only. Adding cross-branch
Devlin edges can alter predecessor types, and an actual finite
pre-diary/absorber has not been constructed here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- Equality of Boolean decisions reflects equality of the
underlying propositions. Kept local to avoid global rewriting. -/
private theorem iff_of_decide_eq
    (p q : Prop) [Decidable p] [Decidable q]
    (h : decide p = decide q) : p ↔ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

/-- Raw cross-branch singleton comparison quantifies over ALL
earlier nodes, including those not occurring on either compared
source branch. -/
def RawCrossOneTypeBelow
    (F : FiniteSignRootedFlipFamily A n ι)
    (s : Nat) (U V : FiniteSignRootedNode A n) : Prop :=
  ∀ X Y : FiniteSignRootedNode A n,
    X.1 < Y.1 → Y.1 < s →
      ((F.rawAmalgam).edge X Y U ↔
       (F.rawAmalgam).edge X Y V)

/-- Two branches which share their node at cut s have the
SAME raw singleton predecessor type whenever the two
corresponding source singleton codes below s agree.
No source role is assumed. -/
theorem rawCrossOneTypeBelow_of_source_codes
    (F : FiniteSignRootedFlipFamily A n ι)
    (i j : ι) (s u v : Nat)
    (hShared : F.node i s = F.node j s)
    (hsu : s ≤ u) (hsv : s ≤ v)
    (hun : u < n) (hvn : v < n)
    (hCode : oneCode (F.graph i) s u =
      oneCode (F.graph j) s v) :
    F.RawCrossOneTypeBelow s (F.node i u) (F.node j v) := by
  classical
  intro X Y hXY hYs
  have hXs : X.1 < s := lt_trans hXY hYs
  have hPrefixX : F.node i X.1 = F.node j X.1 :=
    F.node_prefix_eq_of_terminal_eq i j X.1 s hXs.le hShared
  have hPrefixY : F.node i Y.1 = F.node j Y.1 :=
    F.node_prefix_eq_of_terminal_eq i j Y.1 s hYs.le hShared
  have hSource : (F.graph i).edge X.1 Y.1 u ↔
      (F.graph j).edge X.1 Y.1 v := by
    have hh := congrFun
      (congrFun hCode (⟨X.1,hXs⟩ : Fin s))
      (⟨Y.1,hYs⟩ : Fin s)
    simp only [oneCode, if_pos hXY] at hh
    exact iff_of_decide_eq _ _ hh
  by_cases hX : X = F.node i X.1
  · by_cases hY : Y = F.node i Y.1
    · have hXJ : X = F.node j X.1 := hX.trans hPrefixX
      have hYJ : Y = F.node j Y.1 := hY.trans hPrefixY
      have hI :
          (F.rawAmalgam).edge X Y (F.node i u) ↔
            (F.graph i).edge X.1 Y.1 u := by
        simpa only [← hX, ← hY] using
          (F.rawAmalgam_edge_iff i X.1 Y.1 u
            hXY (by omega) hun)
      have hJ :
          (F.rawAmalgam).edge X Y (F.node j v) ↔
            (F.graph j).edge X.1 Y.1 v := by
        simpa only [← hXJ, ← hYJ] using
          (F.rawAmalgam_edge_iff j X.1 Y.1 v
            hXY (by omega) hvn)
      exact hI.trans (hSource.trans hJ.symm)
    · have hYJ : Y ≠ F.node j Y.1 := by
        intro he
        exact hY (he.trans hPrefixY.symm)
      exact iff_of_false
        (F.rawAmalgam_no_offpath_edge_at_terminal i X Y u
          (Or.inr hY))
        (F.rawAmalgam_no_offpath_edge_at_terminal j X Y v
          (Or.inr hYJ))
  · have hXJ : X ≠ F.node j X.1 := by
      intro he
      exact hX (he.trans hPrefixX.symm)
    exact iff_of_false
      (F.rawAmalgam_no_offpath_edge_at_terminal i X Y u
        (Or.inl hX))
      (F.rawAmalgam_no_offpath_edge_at_terminal j X Y v
        (Or.inl hXJ))

/-- Cross-branch auxiliary ordered-pair type comparison uses
every earlier raw node X with level below the shared cut s. -/
def RawCrossAuxTypeBelow
    (F : FiniteSignRootedFlipFamily A n ι)
    (s : Nat) (U V U' V' : FiniteSignRootedNode A n) : Prop :=
  ∀ X : FiniteSignRootedNode A n, X.1 < s →
    ((F.rawAmalgam).edge X U V ↔
     (F.rawAmalgam).edge X U' V')

/-- Equal source auxiliary codes at a common sign-rooted cut
give the EXACT same raw auxiliary tests on all earlier nodes.
No assumption that the compared pairs lie on one branch is made. -/
theorem rawCrossAuxTypeBelow_of_source_codes
    (F : FiniteSignRootedFlipFamily A n ι)
    (i j : ι) (s u v w z : Nat)
    (hShared : F.node i s = F.node j s)
    (hsu : s ≤ u) (hsw : s ≤ w)
    (huv : u < v) (hwz : w < z)
    (hvn : v < n) (hzn : z < n)
    (hCode : auxCode (F.graph i) s u v =
      auxCode (F.graph j) s w z) :
    F.RawCrossAuxTypeBelow s
      (F.node i u) (F.node i v)
      (F.node j w) (F.node j z) := by
  classical
  intro X hXs
  have hPrefixX : F.node i X.1 = F.node j X.1 :=
    F.node_prefix_eq_of_terminal_eq i j X.1 s hXs.le hShared
  have hSource : (F.graph i).edge X.1 u v ↔
      (F.graph j).edge X.1 w z := by
    have hh := congrFun hCode (⟨X.1,hXs⟩ : Fin s)
    simp only [auxCode] at hh
    exact iff_of_decide_eq _ _ hh
  by_cases hX : X = F.node i X.1
  · have hXJ : X = F.node j X.1 := hX.trans hPrefixX
    have hI :
        (F.rawAmalgam).edge X (F.node i u) (F.node i v) ↔
          (F.graph i).edge X.1 u v := by
      simpa only [← hX] using
        (F.rawAmalgam_edge_iff i X.1 u v
          (by omega) huv hvn)
    have hJ :
        (F.rawAmalgam).edge X (F.node j w) (F.node j z) ↔
          (F.graph j).edge X.1 w z := by
      simpa only [← hXJ] using
        (F.rawAmalgam_edge_iff j X.1 w z
          (by omega) hwz hzn)
    exact hI.trans (hSource.trans hJ.symm)
  · have hXJ : X ≠ F.node j X.1 := by
      intro he
      exact hX (he.trans hPrefixX.symm)
    exact iff_of_false
      (F.rawAmalgam_no_offpath_edge_at_terminal i
        X (F.node i u) v (Or.inl hX))
      (F.rawAmalgam_no_offpath_edge_at_terminal j
        X (F.node j w) z (Or.inl hXJ))

/-- All three predecessor type components at a shared cut:
two singleton coordinates and the full auxiliary pair type. -/
def RawCrossTwoTypeBelow
    (F : FiniteSignRootedFlipFamily A n ι)
    (s : Nat) (U V U' V' : FiniteSignRootedNode A n) : Prop :=
  F.RawCrossOneTypeBelow s U U' ∧
  F.RawCrossOneTypeBelow s V V' ∧
  F.RawCrossAuxTypeBelow s U V U' V'

/-- The exact complete SOURCE full-pair Boolean code,
when equal between two branches sharing the cut node s,
also determines the exact RAW full-pair predecessor tests
against every earlier branch node of the union. -/
theorem rawCrossTwoTypeBelow_of_source_codes
    (F : FiniteSignRootedFlipFamily A n ι)
    (i j : ι) (s u v w z : Nat)
    (hShared : F.node i s = F.node j s)
    (hsu : s ≤ u) (hsw : s ≤ w)
    (huv : u < v) (hwz : w < z)
    (hvn : v < n) (hzn : z < n)
    (hCode : twoCode (F.graph i) s u v =
      twoCode (F.graph j) s w z) :
    F.RawCrossTwoTypeBelow s
      (F.node i u) (F.node i v)
      (F.node j w) (F.node j z) := by
  have hFirst := congrArg Prod.fst hCode
  have hSecond := congrArg Prod.snd hCode
  have hNext := congrArg Prod.fst hSecond
  have hAux := congrArg Prod.snd hSecond
  exact ⟨
    F.rawCrossOneTypeBelow_of_source_codes i j s u w
      hShared hsu hsw (by omega) (by omega) hFirst,
    F.rawCrossOneTypeBelow_of_source_codes i j s v z
      hShared (by omega) (by omega) hvn hzn hNext,
    F.rawCrossAuxTypeBelow_of_source_codes i j
      s u v w z hShared hsu hsw huv hwz hvn hzn hAux⟩

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
