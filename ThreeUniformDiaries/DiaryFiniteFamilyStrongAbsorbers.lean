import ThreeUniformDiaries.DiaryFiniteFlipAbsorptionUpwardClosure
import ThreeUniformDiaries.DiaryFiniteCanonicalStrongAbsorption
import ThreeUniformDiaries.DiaryFiniteBoundedUniversality

/-!
# Track B: one finite target simultaneously absorbs ANY finite family

For a single finite diary A, the verified canonical sign-rooted theorem
constructs a finite full diary B that absorbs A inside EVERY genuine
finite flip of B. The verified upward-closure theorem says strong
absorption survives a protected, bounded all-meet embedding of B into
a larger finite full diary C.

Thus for any finite list of source diaries, independently obtain their
individual finite strong absorbers, take ONE joint finite full diary
containing all absorbers with bounded protected embeddings, and use
upward closure to conclude it absorbs ALL given sources at once.

As a corollary there is one finite full target for every finite full
source diary on a prescribed finite frame [0,n), not merely a separate
absorber for each edge table.

This gives genuine finite UNIFORMITY and can be used when constructing
finite stages of a countable diary, but it does not construct an
extension-compatible chain of copies, an infinite uniform absorber,
or the unresolved countable-source flip property.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Choose the verified strong finite flip absorber of one
finite diary input, retaining its complete genuine finite frame. -/
noncomputable def FiniteDiaryInput.strongFlipAbsorber
    (D : FiniteDiaryInput) : FiniteDiaryInput := by
  classical
  let h := exists_finiteDiary_universal_flip_absorber D.diary
  exact ⟨Classical.choose h,
    Classical.choose (Classical.choose_spec h),
    (Classical.choose_spec (Classical.choose_spec h)).1⟩

/-- The chosen individual target really absorbs its finite source
under ALL genuine flips, with the entire source inside its
bounded frame and all mixed numerical meets preserved. -/
theorem FiniteDiaryInput.strongFlipAbsorber_absorbs
    (D : FiniteDiaryInput) :
    AbsorbsEveryTargetFlipInside
      D.graph D.strongFlipAbsorber.graph
      D.bound D.strongFlipAbsorber.bound := by
  classical
  let h := exists_finiteDiary_universal_flip_absorber D.diary
  exact (Classical.choose_spec
    (Classical.choose_spec h)).2

/-- A single GENUINE FINITE full diary absorbs every member of
an arbitrary finite list of full diary sources under every flip
of the SAME target. No coherence or relative extension premise
is introduced, and the family may contain repeated source sizes. -/
theorem exists_finiteDiary_absorbing_finiteFamily
    (Ds : List FiniteDiaryInput) :
    ∃ (T : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock T k ∧
      ∀ D : FiniteDiaryInput, D ∈ Ds →
        AbsorbsEveryTargetFlipInside D.graph T D.bound k := by
  classical
  let Xs : List FiniteDiaryInput :=
    Ds.map FiniteDiaryInput.strongFlipAbsorber
  obtain ⟨T,k,DT,hCopies⟩ :=
    exists_finiteDiary_for_finiteFamily_bounded Xs
  refine ⟨T,k,DT,?_⟩
  intro D hD
  have hMem : D.strongFlipAbsorber ∈ Xs := by
    apply List.mem_map.mpr
    exact ⟨D,hD,rfl⟩
  obtain ⟨f,E⟩ := hCopies D.strongFlipAbsorber hMem
  exact absorbsEveryTargetFlipInside_of_target_embedding
    D.strongFlipAbsorber.diary
    D.strongFlipAbsorber_absorbs E

/-- Uniform strong finite absorption at a fixed source SIZE:
one finite target works for every finite full diary on [0,n),
including every genuine source flip and all edge/nonedge tables.

This strengthens the per-source strong finite absorber theorem by
exchanging the quantifiers:
  forall source A (exists target B)  ==>  exists target B (forall A)
for a FIXED finite source size n. The exchange is justified by
finite enumerability of all actual finite source edge codes, not
by any infinite compactness or noncompact candidate completion. -/
theorem exists_finiteDiary_universal_strong_absorber_at_size
    (n : Nat) :
    ∃ (T : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock T k ∧
      ∀ A : Ordered3Graph Nat,
        FiniteRoleDiaryBlock A n →
        AbsorbsEveryTargetFlipInside A T n k := by
  classical
  obtain ⟨T,k,DT,hAll⟩ :=
    exists_finiteDiary_absorbing_finiteFamily (finiteDiaryCodeInputs n)
  refine ⟨T,k,DT,?_⟩
  intro A DA
  obtain ⟨D,hD,hGraph,hBound⟩ :=
    finiteDiaryCodeInputs_covers n A DA
  have hAbs : AbsorbsEveryTargetFlipInside
      D.graph T D.bound k := hAll D hD
  simpa only [hGraph,hBound] using hAbs

end DiaryLeafPriority
end ThreeUniformDiaries
