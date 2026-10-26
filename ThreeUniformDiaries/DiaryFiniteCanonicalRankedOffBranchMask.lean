import ThreeUniformDiaries.DiaryFiniteCanonicalRankedRawGraph
import ThreeUniformDiaries.DiaryCausalOriginalMeetPreservation

/-!
# The actual sign-rooted off-branch mask on the consecutive Nat ranks

The earlier sign-rooted results prove ordered off-branch mask
coherence on the FINITE raw-node type; causal literal-V3 recursion
requires a mask on Nat. The canonical predecessor-count rank now
bridges those representations, with no new combinatorial hypothesis.

Each actual node is assigned its rank in Fin(card carrier). This
rank is a BIJECTION onto the consecutive initial interval.
The raw ordered off-branch predicate induces an honest mask
M : Nat -> Nat -> Prop supported exactly on pairs of realised
ranked nodes. It is strictly increasing in the two rank indices,
never selects two original nodes on one source branch, and never
selects a split-level node as its middle coordinate.

Most importantly, at a shared original source split s, every
ranked vertex below the split's finite index has the SAME mask
against corresponding later leaf terminals. Surjectivity of the
rank enumeration handles every Nat index below the cut, not merely
those for which an original node was explicitly supplied.
This exports the literal SameEarlierMarkerMask prerequisite
of the causal original-meet and original-branch V3 theorems.

The rank-indexed RAW graph and mask are now genuine Nat objects.
Proving the RAW singleton meet exactly equals the rank of its
original split, and instantiating the resulting final diary axioms,
remain separate obligations. No unrestricted absorber is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finite strict total order is enumerated by counting
predecessors: the previously verified injective rank is also
surjective onto Fin(card carrier). -/
theorem finiteCanonicalNodeIndex_surjective
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    Function.Surjective (finiteCanonicalNodeIndex DA) := by
  exact (Finite.injective_iff_surjective_of_equiv
    (Fintype.equivFin (FiniteCanonicalSignRootedVertex DA))).mp
    (finiteCanonicalNodeIndex_injective DA)

/-- On two realised canonical vertices, the canonical
subtype order is exactly the ambient level-first relation. -/
theorem finiteCanonicalNodeBefore_iff_ambient
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y : FiniteCanonicalSignRootedVertex DA) :
    finiteCanonicalNodeBefore DA X Y ↔
      finiteCanonicalNodeBeforeAmbient DA X.val Y.val := by
  constructor
  · intro h
    rcases h with hLevel | ⟨hTie,hRank⟩
    · exact Or.inl hLevel
    · exact Or.inr
        ⟨hTie,⟨X.property,Y.property,Or.inr ⟨hTie,hRank⟩⟩⟩
  · intro h
    rcases h with hLevel | ⟨_,hExternal⟩
    · exact Or.inl hLevel
    · obtain ⟨hx,hy,hSub⟩ := hExternal
      have hX : (⟨X.val,hx⟩ : FiniteCanonicalSignRootedVertex DA) = X :=
        Subtype.ext rfl
      have hY : (⟨Y.val,hy⟩ : FiniteCanonicalSignRootedVertex DA) = Y :=
        Subtype.ext rfl
      simpa only [hX,hY] using hSub

/-- The numerical predecessor-count rank remembers the
strict finite order in BOTH directions. -/
theorem finiteCanonicalNodeBefore_iff_rank_lt
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y : FiniteCanonicalSignRootedVertex DA) :
    finiteCanonicalNodeBefore DA X Y ↔
      (finiteCanonicalNodeIndex DA X).val <
        (finiteCanonicalNodeIndex DA Y).val := by
  constructor
  · exact finiteCanonicalNodeIndex_lt_of_before DA
  · intro hXY
    by_cases hEq : X = Y
    · subst Y
      omega
    · rcases finiteCanonicalNodeBefore_total_of_ne
        DA X Y hEq with hBefore | hAfter
      · exact hBefore
      · have hWrong := finiteCanonicalNodeIndex_lt_of_before
          DA hAfter
        omega

/-- The EXACT mask of missing off-branch Devlin markers
transported from finite raw nodes to their Nat rank indices. -/
noncomputable def finiteCanonicalRankedOffBranchMask
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (y z : Nat) : Prop :=
  ∃ Y Z : FiniteCanonicalSignRootedVertex DA,
    (finiteCanonicalNodeIndex DA Y).val = y ∧
    (finiteCanonicalNodeIndex DA Z).val = z ∧
    (finiteCanonicalSignRootedFamily DA).OrderedOffBranchLeafPair
      (finiteCanonicalNodeBeforeAmbient DA) Y.val Z.val

/-- At actual finite vertices, the Nat mask is identical
to the original geometric ordered off-branch predicate. -/
theorem finiteCanonicalRankedOffBranchMask_iff
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (Y Z : FiniteCanonicalSignRootedVertex DA) :
    finiteCanonicalRankedOffBranchMask DA
      (finiteCanonicalNodeIndex DA Y).val
      (finiteCanonicalNodeIndex DA Z).val ↔
    (finiteCanonicalSignRootedFamily DA).OrderedOffBranchLeafPair
      (finiteCanonicalNodeBeforeAmbient DA) Y.val Z.val := by
  constructor
  · rintro ⟨Y',Z',hY,hZ,hOff⟩
    have eY : Y' = Y := finiteCanonicalNodeIndex_injective DA
      (Fin.ext hY)
    have eZ : Z' = Z := finiteCanonicalNodeIndex_injective DA
      (Fin.ext hZ)
    subst Y'
    subst Z'
    exact hOff
  · intro h
    exact ⟨Y,Z,rfl,rfl,h⟩

/-- Every selected marker pair has STRICTLY increasing
indices in the actual finite enumeration. -/
theorem finiteCanonicalRankedOffBranchMask_later
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (y z : Nat)
    (hm : finiteCanonicalRankedOffBranchMask DA y z) :
    y < z := by
  obtain ⟨Y,Z,hY,hZ,hOff⟩ := hm
  have hBefore :
      finiteCanonicalNodeBefore DA Y Z :=
    (finiteCanonicalNodeBefore_iff_ambient DA Y Z).mpr
      hOff.ordered
  have hRank := finiteCanonicalNodeIndex_lt_of_before DA hBefore
  rw [hY,hZ] at hRank
  exact hRank

/-- A genuine original branch pair is never selected by
the new Nat-indexed off-branch marker mask. -/
theorem finiteCanonicalRankedOffBranchMask_same_branch_false
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (u v : Nat) (huv : u < v) (hvn : v < n) :
    ¬ finiteCanonicalRankedOffBranchMask DA
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i u (by omega))).val
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i v hvn)).val := by
  intro h
  have hActual := (finiteCanonicalRankedOffBranchMask_iff DA
    (finiteCanonicalNodeAt DA i u (by omega))
    (finiteCanonicalNodeAt DA i v hvn)).mp h
  exact ((finiteCanonicalSignRootedFamily DA).
    orderedOffBranch_same_source_branch_false
      (finiteCanonicalNodeBeforeAmbient DA) i u v huv hvn) hActual

/-- The actual mask NEVER selects a split-node index as
middle coordinate, even if a source level occurs in
many different sign-rooted prefix branches. -/
theorem finiteCanonicalRankedOffBranchMask_split_middle_false
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (s : Nat) (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (hsn : s < n) (z : Nat) :
    ¬ finiteCanonicalRankedOffBranchMask DA
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i s hsn)).val z := by
  rintro ⟨Y,Z,hY,_,hOff⟩
  have eY : Y = finiteCanonicalNodeAt DA i s hsn :=
    finiteCanonicalNodeIndex_injective DA (Fin.ext hY)
  subst Y
  have hYLevel : (finiteCanonicalNodeAt DA i s hsn).val.1 = s := by
    simp only [finiteCanonicalNodeAt,
      FiniteSignRootedFlipFamily.node_level]
  exact ((finiteCanonicalSignRootedFamily DA).
    orderedOffBranch_splitLevel_middle_false
      (finiteCanonicalNodeBeforeAmbient DA) s hs
      (finiteCanonicalNodeAt DA i s hsn).val Z.val hYLevel)
      hOff

/-- At every ACTUAL ranked predecessor of a shared split,
the two genuine source terminal masks coincide, including
tied original levels and raw vertices off both branches. -/
theorem finiteCanonicalRankedOffBranchMask_sharedSplit_predecessor
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (hsn : s < n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (Y : FiniteCanonicalSignRootedVertex DA)
    (hYS :
      (finiteCanonicalNodeIndex DA Y).val <
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val) :
    finiteCanonicalRankedOffBranchMask DA
      (finiteCanonicalNodeIndex DA Y).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val ↔
    finiteCanonicalRankedOffBranchMask DA
      (finiteCanonicalNodeIndex DA Y).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j v hvn)).val := by
  have hBefore :
      finiteCanonicalNodeBefore DA Y
        (finiteCanonicalNodeAt DA i s hsn) :=
    (finiteCanonicalNodeBefore_iff_rank_lt DA Y
      (finiteCanonicalNodeAt DA i s hsn)).mpr hYS
  have hAmbient :
      finiteCanonicalNodeBeforeAmbient DA Y.val
        ((finiteCanonicalSignRootedFamily DA).node i s) :=
    (finiteCanonicalNodeBefore_iff_ambient DA Y
      (finiteCanonicalNodeAt DA i s hsn)).mp hBefore
  have hRaw := finiteCanonicalSignRooted_orderedMask_sharedSplit
    DA i j s u v hs hShared hsu hsv hun hvn hu hv Y.val hAmbient
  exact (finiteCanonicalRankedOffBranchMask_iff DA Y
    (finiteCanonicalNodeAt DA i u hun)).trans
      (hRaw.trans
        (finiteCanonicalRankedOffBranchMask_iff DA Y
          (finiteCanonicalNodeAt DA j v hvn)).symm)

/-- The genuine Nat-indexed mask satisfies precisely the
SameEarlierMarkerMask hypothesis needed in the causal
original-meet and V3 transport theorems, for EVERY Nat
predecessor of a shared source split. -/
theorem finiteCanonicalRankedOffBranchMask_sharedSplit_below
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (hsn : s < n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v) :
    SameEarlierMarkerMask
      (finiteCanonicalRankedOffBranchMask DA)
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j v hvn)).val := by
  intro y hBefore
  have hyBound : y < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    lt_trans hBefore
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).isLt
  obtain ⟨Y,hY⟩ := finiteCanonicalNodeIndex_surjective DA
    (⟨y,hyBound⟩ : Fin (Fintype.card
      (FiniteCanonicalSignRootedVertex DA)))
  have hYval : (finiteCanonicalNodeIndex DA Y).val = y :=
    congrArg Fin.val hY
  have hYS :
      (finiteCanonicalNodeIndex DA Y).val <
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val := by
    simpa only [hYval] using hBefore
  have hMask := finiteCanonicalRankedOffBranchMask_sharedSplit_predecessor
    DA i j s u v hs hsn hShared hsu hsv hun hvn hu hv Y hYS
  simpa only [hYval] using hMask

end DiaryLeafPriority
end ThreeUniformDiaries
