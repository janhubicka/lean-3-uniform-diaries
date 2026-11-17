import ThreeUniformDiaries.DiaryCanonicalMarkedRestrictionFactor
import ThreeUniformDiaries.DiaryFiniteSupportInverseRank

/-!
# Concrete raw restriction of a marked finite diary code

A marked A-source carries its COMPLETE finite enumerated source picture
and the actual rank of each labelled A-leaf. To select a B-subtuple,
take its marked leaves in that source, include 0,1,2 and every genuine
S1 / full ordered-pair S2 generator, and re-enumerate the support.

This construction produces an ACTUAL MarkedFiniteSource 0 b,
without any extra choice of an ambient countable diary.

The theorem below only states the exact rank/mark transport.
It does NOT yet certify that the result is a genuine finite full
B-diary: that needs the finite extraction / realization-independence
argument. In particular no circular BRS or diary Ramsey assumption
is used here.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open DiaryLeafPriority

/-- Selected source leaves of the restricted marked tuple,
computed in the finite source picture of P. Label maps may
permute the numerical order. -/
noncomputable def markedRestrictionLeaves
    {a b : Nat} (P : MarkedFiniteSource 0 a)
    (i : Fin b → Fin a) : Finset Nat :=
  (Finset.univ : Finset (Fin b)).image (fun j => (P.marked (i j)).val)

/-- The full S1/S2 finite support of the selected marked leaves,
including the three markers and exact capped meet generators. -/
noncomputable def markedRestrictionSupport
    {a b : Nat} (P : MarkedFiniteSource 0 a)
    (i : Fin b → Fin a) : Finset Nat :=
  finiteLeafMeetSupport P.source.picture.toOrdered3Graph
    (markedRestrictionLeaves P i)

/-- An ACTUAL finite marked source is obtained by closing the
selected leaves and canonically reindexing. The stage size is
positive since the closure always contains 0,1,2. Membership
in the GENUINE marked-diary family is a separate next lemma. -/
noncomputable def MarkedFiniteSource.rawRestrict
    {a b : Nat} (P : MarkedFiniteSource 0 a)
    (i : Fin b → Fin a) : MarkedFiniteSource 0 b := by
  classical
  let H : Ordered3Graph Nat := P.source.picture.toOrdered3Graph
  let L : Finset Nat := markedRestrictionLeaves P i
  let S : Finset Nat := finiteLeafMeetSupport H L
  have hCard : 1 ≤ S.card := by
    change 1 ≤ (finiteLeafMeetSupport H L).card
    exact (by decide : 1 ≤ 3).trans
      (finiteLeafMeetSupport_reindex_markers H L).1
  have hk : S.card - 1 + 1 = S.card := Nat.sub_add_cancel hCard
  let source : ProtectedSource 0 := {
    k := S.card - 1
    picture := hk.symm ▸ ((finiteSupportGraph H S).initialSegment S.card)
    cut_le := by omega
  }
  have hSize : source.k + 1 = S.card := hk
  let marked : Fin b → Fin (source.k + 1) := fun j => by
    have hLeaf : (P.marked (i j)).val ∈ S := by
      change (P.marked (i j)).val ∈ finiteLeafMeetSupport H L
      apply mem_finiteLeafMeetSupport_leaf H L
      exact Finset.mem_image.mpr
        ⟨j, Finset.mem_univ _, rfl⟩
    exact Fin.cast hSize.symm
      ⟨finiteSupportRank S (P.marked (i j)).val,
       (finiteSupportRank_spec S _ hLeaf).1⟩
  exact ⟨source, marked⟩

/-- The raw restricted source records the exact ORIGINAL numeric
rank of each marked B-leaf inside the selected S1/S2 support. -/
theorem MarkedFiniteSource.rawRestrict_marked_rank
    {a b : Nat} (P : MarkedFiniteSource 0 a)
    (i : Fin b → Fin a) (j : Fin b) :
    ((P.rawRestrict i).marked j).val =
      finiteSupportRank (markedRestrictionSupport P i)
        (P.marked (i j)).val := by
  rfl

/-- Reading each restricted mark through the canonical increasing
support enumeration returns exactly the selected old marked leaf,
not merely an isomorphic or unlabelled diagram. -/
theorem MarkedFiniteSource.rawRestrict_marked_value
    {a b : Nat} (P : MarkedFiniteSource 0 a)
    (i : Fin b → Fin a) (j : Fin b) :
    finiteSupportIndex (markedRestrictionSupport P i)
        ((P.rawRestrict i).marked j).val =
      (P.marked (i j)).val := by
  rw [P.rawRestrict_marked_rank i j]
  apply (finiteSupportRank_spec
      (markedRestrictionSupport P i)
      (P.marked (i j)).val ?_).2
  change (P.marked (i j)).val ∈
    finiteLeafMeetSupport P.source.picture.toOrdered3Graph
      (markedRestrictionLeaves P i)
  apply mem_finiteLeafMeetSupport_leaf
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
