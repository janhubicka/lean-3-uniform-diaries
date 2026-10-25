import ThreeUniformDiaries.DiaryFiniteCanonicalSignRootedCarrier
import ThreeUniformDiaries.DiaryFiniteSignRootedOrderedMarkerComparison

/-!
# A concrete level-first strict total order on the finite raw flip carrier

The canonical sign-rooted carrier has a finite set of realised
nodes. Multiple distinct nodes can have the SAME original source
level, so a final diary enumeration must order those nodes too.

Select a noncomputable injection of the finite carrier into
a finite initial segment using Fintype.equivFin. Order nodes
LEXICOGRAPHICALLY by
  (original source level, arbitrary finite tie rank).

This gives a strict total order on the ACTUAL finite carrier,
extends every strict source-level inequality, and therefore
makes the image of EVERY original source flip branch strictly
increasing. It also resolves all ties between distinct raw
nodes, including tied leaf nodes requiring Devlin markers.

The order is not claimed to satisfy any V3 orientation constraint;
that is a separate causal marker-choice problem. The finite
ordered carrier has not been converted to a bounded Nat-indexed
V/E pre-diary here, and no absorber existence is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The finite type of all ACTUAL canonical sign-rooted nodes. -/
abbrev FiniteCanonicalSignRootedVertex
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :=
  {X : FiniteSignRootedNode A n //
    X ∈ finiteCanonicalSignRootedNodeSet DA}

/-- Injective, source-independent tie rank on the finite
canonical node set. Its particular values are irrelevant. -/
noncomputable def finiteCanonicalNodeTieRank
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X : FiniteCanonicalSignRootedVertex DA) : Nat := by
  classical
  exact ((Fintype.equivFin (FiniteCanonicalSignRootedVertex DA)) X).val

theorem finiteCanonicalNodeTieRank_injective
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    Function.Injective (finiteCanonicalNodeTieRank DA) := by
  classical
  intro X Y h
  have hFin :
      (Fintype.equivFin (FiniteCanonicalSignRootedVertex DA)) X =
      (Fintype.equivFin (FiniteCanonicalSignRootedVertex DA)) Y := by
    apply Fin.ext
    exact h
  exact (Fintype.equivFin
    (FiniteCanonicalSignRootedVertex DA)).injective hFin

/-- The promised source-level-first strict order, with
ties broken by the injective finite canonical rank. -/
noncomputable def finiteCanonicalNodeBefore
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y : FiniteCanonicalSignRootedVertex DA) : Prop :=
  X.val.1 < Y.val.1 ∨
    (X.val.1 = Y.val.1 ∧
      finiteCanonicalNodeTieRank DA X <
        finiteCanonicalNodeTieRank DA Y)

theorem finiteCanonicalNodeBefore_irrefl
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X : FiniteCanonicalSignRootedVertex DA) :
    ¬ finiteCanonicalNodeBefore DA X X := by
  unfold finiteCanonicalNodeBefore
  omega

theorem finiteCanonicalNodeBefore_trans
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y Z : FiniteCanonicalSignRootedVertex DA)
    (hXY : finiteCanonicalNodeBefore DA X Y)
    (hYZ : finiteCanonicalNodeBefore DA Y Z) :
    finiteCanonicalNodeBefore DA X Z := by
  unfold finiteCanonicalNodeBefore at *
  omega

/-- Every two DISTINCT realised nodes are comparable by the
source-level-first order, including nodes tied at one level. -/
theorem finiteCanonicalNodeBefore_total_of_ne
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y : FiniteCanonicalSignRootedVertex DA)
    (hXY : X ≠ Y) :
    finiteCanonicalNodeBefore DA X Y ∨
      finiteCanonicalNodeBefore DA Y X := by
  have hRank :
      finiteCanonicalNodeTieRank DA X ≠
        finiteCanonicalNodeTieRank DA Y := by
    intro h
    exact hXY (finiteCanonicalNodeTieRank_injective DA h)
  unfold finiteCanonicalNodeBefore
  omega

/-- This total order refines all comparisons of original
source levels, independently of how ties are enumerated. -/
theorem finiteCanonicalNodeBefore_of_level_lt
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y : FiniteCanonicalSignRootedVertex DA)
    (hLevel : X.val.1 < Y.val.1) :
    finiteCanonicalNodeBefore DA X Y :=
  Or.inl hLevel

/-- The source-level-first order can also be viewed as a
relation on the entire raw Node type, using membership
witnesses. Only ACTUAL finite carrier members are ordered. -/
noncomputable def finiteCanonicalNodeBeforeExternal
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y : FiniteSignRootedNode A n) : Prop :=
  ∃ (hx : X ∈ finiteCanonicalSignRootedNodeSet DA)
    (hy : Y ∈ finiteCanonicalSignRootedNodeSet DA),
      finiteCanonicalNodeBefore DA ⟨X,hx⟩ ⟨Y,hy⟩

/-- Every branch maps increasing original source vertices
to increasing ACTUAL raw nodes in this total ordering. -/
theorem finiteCanonicalNodeBefore_source_branch
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (c : FiniteCanonicalFlipIndex A n)
    (x y : Nat) (hxy : x < y) (hyn : y < n) :
    finiteCanonicalNodeBeforeExternal DA
      ((finiteCanonicalSignRootedFamily DA).node c x)
      ((finiteCanonicalSignRootedFamily DA).node c y) := by
  have hxn : x < n := by omega
  have hx := finiteCanonicalSignRootedNodeSet_contains
    DA c x hxn
  have hy := finiteCanonicalSignRootedNodeSet_contains
    DA c y hyn
  refine ⟨hx,hy,?_⟩
  exact finiteCanonicalNodeBefore_of_level_lt DA
    ⟨(finiteCanonicalSignRootedFamily DA).node c x,hx⟩
    ⟨(finiteCanonicalSignRootedFamily DA).node c y,hy⟩
    (by simpa only [FiniteSignRootedFlipFamily.node_level]
      using hxy)


/-- A TOTAL-ORDER CANDIDATE relation on the ambient raw node type:
strictly smaller source levels are ordered first even outside
the finite realised carrier, and source-level ties inside the
carrier are broken by the finite canonical tie rank. -/
noncomputable def finiteCanonicalNodeBeforeAmbient
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y : FiniteSignRootedNode A n) : Prop :=
  X.1 < Y.1 ∨
    (X.1 = Y.1 ∧ finiteCanonicalNodeBeforeExternal DA X Y)

/-- Unlike the restricted external subtype order, this ambient
relation satisfies the source-level monotonicity hypothesis of
the ordered Devlin-marker stability theorem ON ALL raw nodes. -/
theorem finiteCanonicalNodeBeforeAmbient_extends_levels
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    (finiteCanonicalSignRootedFamily DA).ExtendsSourceLevels
      (finiteCanonicalNodeBeforeAmbient DA) := by
  intro X Y hXY
  exact Or.inl hXY

/-- Any two DISTINCT members of the finite canonical raw carrier
are comparable by the ambient order (ties included). -/
theorem finiteCanonicalNodeBeforeAmbient_total_on_carrier
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y : FiniteSignRootedNode A n)
    (hX : X ∈ finiteCanonicalSignRootedNodeSet DA)
    (hY : Y ∈ finiteCanonicalSignRootedNodeSet DA)
    (hNe : X ≠ Y) :
    finiteCanonicalNodeBeforeAmbient DA X Y ∨
      finiteCanonicalNodeBeforeAmbient DA Y X := by
  let x : FiniteCanonicalSignRootedVertex DA := ⟨X,hX⟩
  let y : FiniteCanonicalSignRootedVertex DA := ⟨Y,hY⟩
  have hxy : x ≠ y := by
    intro h
    exact hNe (congrArg Subtype.val h)
  rcases finiteCanonicalNodeBefore_total_of_ne DA x y hxy with
      hBefore | hAfter
  · change
      X.1 < Y.1 ∨
      (X.1 = Y.1 ∧
        finiteCanonicalNodeTieRank DA x <
          finiteCanonicalNodeTieRank DA y) at hBefore
    rcases hBefore with hLevel | hTie
    · exact Or.inl (Or.inl hLevel)
    · exact Or.inl (Or.inr
        ⟨hTie.1,⟨hX,hY,Or.inr hTie⟩⟩)
  · change
      Y.1 < X.1 ∨
      (Y.1 = X.1 ∧
        finiteCanonicalNodeTieRank DA y <
          finiteCanonicalNodeTieRank DA x) at hAfter
    rcases hAfter with hLevel | hTie
    · exact Or.inr (Or.inl hLevel)
    · exact Or.inr (Or.inr
        ⟨hTie.1,⟨hY,hX,Or.inr hTie⟩⟩)

end DiaryLeafPriority
end ThreeUniformDiaries
