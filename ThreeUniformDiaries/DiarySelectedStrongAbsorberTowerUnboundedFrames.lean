import ThreeUniformDiaries.DiaryUniversalFiniteStrongAbsorberTower
import ThreeUniformDiaries.DiaryExistenceFiniteExactLeafReduct

/-!
# Track B: actual selected finite absorber tower has UNBOUNDED frame sizes

Two existing verified results suffice:
* every finite ordered 3-hypergraph on r+4 vertices has an exact
  finite full diary representation with r+4 genuine leaves;
* at the appropriate stage the selected strong-absorber tower
  absorbs every genuine full finite source of that source frame size.

Any absorbing target therefore contains a genuine bounded
strictly increasing copy of an arbitrarily large finite full diary.
Its finite frame must be at least as large as the source frame.

This proves the unbounded-frame precondition of the proposed
Nat carrier/prefix-stabilisation criteria unconditionally, for
the ACTUAL selected absorber tower. It does NOT imply bounded
forward ranks, construct a full RoleDiary colimit, or produce
compatible embeddings of growing source diaries.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any globally strictly increasing map Nat -> Nat lies above
the numerical identity. -/
private theorem nat_le_of_strictMono
    (f : Nat → Nat) (hf : StrictMono f) :
    ∀ u : Nat, u ≤ f u := by
  intro u
  induction u with
  | zero =>
      omega
  | succ u ih =>
      have hstep : f u < f (u+1) := hf (by omega)
      omega

/-- For every R there is a genuine finite full diary with an
actual bounded frame containing at least R+4 distinct vertices.
We use the existing EXACT finite leaf-reduct theorem, not an
unproved "finite diaries of every exact frame size" claim. -/
theorem exists_finiteFullDiary_arbitrarily_large_frame
    (R : Nat) :
    ∃ (A : Ordered3Graph Nat) (n : Nat),
      FiniteRoleDiaryBlock A n ∧ R+4 ≤ n := by
  obtain ⟨A,n,f,hDiary,hMono,hLeaves,_,_⟩ :=
    exists_finite_diary_with_exact_induced_leaf_prefix
      finiteEmptyThree (R+4)
  have hLast : f (R+3) < n :=
    (hLeaves (R+3) (by omega)).1
  have hLower : R+3 ≤ f (R+3) :=
    nat_le_of_strictMono f hMono (R+3)
  refine ⟨A,n,hDiary,?_⟩
  omega

/-- The fixed, selected, REAL finite strong absorber tower is
unbounded in its actual frame sizes. Every stage still consists
of a genuine finite full diary, and no new transition selection
or hypothesis on future rank motion is introduced. -/
theorem universalStrongAbsorberTower_unbounded_frame :
    ∀ R : Nat, ∃ j : Nat,
      R < (universalStrongAbsorberTower j).bound := by
  intro R
  obtain ⟨A,n,hDiary,hN⟩ :=
    exists_finiteFullDiary_arbitrarily_large_frame R
  have hn : 4 ≤ n := by omega
  let j : Nat := n-3
  let B : FiniteDiaryInput := universalStrongAbsorberTower j
  have hAbs : AbsorbsEveryTargetFlipInside
      A B.graph n B.bound := by
    exact universalStrongAbsorberTower_absorbs_any_finite_size
      n j hn (by dsimp [j]; omega) A hDiary
  have hFlip : FiniteDiaryFlip B.graph B.graph B.bound :=
    FiniteDiaryFlip.refl B.diary
  obtain ⟨f,Ef⟩ := hAbs B.graph hFlip
  have hLast : f (n-1) < B.bound :=
    Ef.image_bound (n-1) (by omega)
  have hLower : n-1 ≤ f (n-1) :=
    nat_le_of_strictMono f Ef.toMeetEmbedding.strictMono (n-1)
  refine ⟨j,?_⟩
  dsimp [B] at hLast
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
