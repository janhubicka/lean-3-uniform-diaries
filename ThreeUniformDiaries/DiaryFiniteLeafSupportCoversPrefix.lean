import ThreeUniformDiaries.DiaryFiniteSupportProtectedPrefixRanks
import ThreeUniformDiaries.DiaryCountableCofinalFiniteSupports

/-!
# Track B: every finite countable diary prefix survives full finite compression

The previously CI-verified cofinal finite-support theorem already
shows that EVERY finite set of vertices of a countable full RoleDiary
is contained in a finite leaf-meet support, and that the increasing
reindexed support is a genuine FINITE full diary.

We therefore reuse that theorem rather than duplicating the V1/V2
witness induction and finite support monotonicity. The genuinely new
conclusion here is LITERAL preservation of the entire prescribed
numerical prefix [0,p) under increasing rank compression, using
the verified fixed-prefix index and rank lemmas.

This does not claim a literal proper full-finite-diary end extension:
the retained prefix of a COUNTABLE diary is not assumed to satisfy
the complete finite full diary axioms on its own.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any full countable RoleDiary has a genuine full FINITE
leaf-meet compression retaining a prescribed finite numerical
prefix with EXACTLY the original ranks and all its vertices
inside the true bounded finite frame. -/
theorem RoleDiary.exists_finite_full_diary_retaining_prefix
    {G : Ordered3Graph Nat} (DG : RoleDiary G)
    (p : Nat) :
    ∃ L : Finset Nat,
      (∀ u : Nat, u ∈ L → IsLeaf G u) ∧
      FiniteRoleDiaryBlock
        (finiteSupportGraph G (finiteLeafMeetSupport G L))
        (finiteLeafMeetSupport G L).card ∧
      (∀ u : Nat, u < p →
        u < (finiteLeafMeetSupport G L).card ∧
        finiteSupportIndex (finiteLeafMeetSupport G L) u = u) := by
  classical
  obtain ⟨m,hCover⟩ :=
    countableDiaryFiniteSupport_contains_finset DG (Finset.range p)
  let L : Finset Nat := countableDiaryLeafPrefix G m
  let S : Finset Nat := finiteLeafMeetSupport G L
  have hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u := by
    intro u hu
    exact ((mem_countableDiaryLeafPrefix_iff G m u).mp hu).2.2
  have hPrefix : ∀ u : Nat, u < p → u ∈ S := by
    intro u hu
    exact hCover u (Finset.mem_range.mpr hu)
  have hDiary : FiniteRoleDiaryBlock (finiteSupportGraph G S) S.card := by
    simpa only [S,L,countableDiaryFiniteSupport] using
      (countableDiaryFiniteSupport_is_finiteDiary DG m)
  refine ⟨L,hLeaves,hDiary,?_⟩
  intro u hu
  have hSpec := finiteSupportRank_spec S u (hPrefix u hu)
  have hRank := finiteSupportRank_fixed_prefix S p hPrefix u hu
  rw [hRank] at hSpec
  exact ⟨hSpec.1,finiteSupportIndex_fixed_prefix S p hPrefix u hu⟩

end DiaryLeafPriority
end ThreeUniformDiaries
