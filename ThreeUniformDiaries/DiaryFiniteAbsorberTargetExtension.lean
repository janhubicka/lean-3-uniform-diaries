import ThreeUniformDiaries.DiaryFiniteFamilyStrongAbsorbers

/-!
# Track B: extend ANY finite diary to absorb a chosen finite source family

The verified finite bounded-family joint-embedding theorem lets us keep
an existing finite target B as ONE protected copy in a larger finite
full diary C. Independently, the strong flip absorber theorem gives
one absorber for each member of a finite list Ds. Jointly embed B and
those finitely many absorbers into the SAME C, then transfer strong
target-flip absorption along the protected copies.

Hence a finite target may be enlarged to absorb ANY finite family
without losing its old protected full-meet diagram. Taking the
finite list of ALL source diary codes on a fixed frame n yields a
relative target-extension statement universal at that finite size.

IMPORTANT: the protected embedding B -> C is existentially chosen.
It is NOT required to preserve a prescribed earlier embedding or
an arbitrary finite set of target vertex images. This is a target-side
finite extension theorem, not the open source-prefix relative
extension needed for countable-source flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Extend one EXISTING finite full target B to a new finite
full target C which contains a bounded protected copy of B
and absorbs all prescribed finite sources under EVERY genuine
target flip. The copy of B into C is existential, not fixed. -/
theorem exists_finiteDiary_extension_absorbing_finiteFamily
    (B : FiniteDiaryInput) (Ds : List FiniteDiaryInput) :
    ∃ (C : Ordered3Graph Nat) (l : Nat),
      FiniteRoleDiaryBlock C l ∧
      (∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding B.graph C B.bound l f) ∧
      (∀ D : FiniteDiaryInput, D ∈ Ds →
        AbsorbsEveryTargetFlipInside D.graph C D.bound l) := by
  classical
  let Xs : List FiniteDiaryInput :=
    B :: Ds.map FiniteDiaryInput.strongFlipAbsorber
  obtain ⟨C,l,DC,hCopies⟩ :=
    exists_finiteDiary_for_finiteFamily_bounded Xs
  obtain ⟨fB,EB⟩ := hCopies B (by simp [Xs])
  refine ⟨C,l,DC,⟨fB,EB⟩,?_⟩
  intro D hD
  have hMem : D.strongFlipAbsorber ∈ Xs := by
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨D,hD,rfl⟩
  obtain ⟨fD,ED⟩ := hCopies D.strongFlipAbsorber hMem
  exact absorbsEveryTargetFlipInside_of_target_embedding
    D.strongFlipAbsorber.diary
    D.strongFlipAbsorber_absorbs ED

/-- Uniform finite-size extension: choose ANY existing finite
full diary B and a source frame size n. There is a larger finite
full C with a protected bounded copy of B and such that EVERY
genuine n-vertex full diary A is contained in EVERY genuine
flip of C by a bounded all-meet embedding.

This combines preservation of an existential old target copy
and strong finite source universality. It does not retain fixed
old vertex ranks or construct compatible countable source copies.
-/
theorem exists_finiteDiary_extension_universal_strong_at_size
    (B : FiniteDiaryInput) (n : Nat) :
    ∃ (C : Ordered3Graph Nat) (l : Nat),
      FiniteRoleDiaryBlock C l ∧
      (∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding B.graph C B.bound l f) ∧
      (∀ A : Ordered3Graph Nat,
        FiniteRoleDiaryBlock A n →
          AbsorbsEveryTargetFlipInside A C n l) := by
  classical
  obtain ⟨C,l,DC,hB,hAbs⟩ :=
    exists_finiteDiary_extension_absorbing_finiteFamily
      B (finiteDiaryCodeInputs n)
  refine ⟨C,l,DC,hB,?_⟩
  intro A DA
  obtain ⟨D,hD,hGraph,hBound⟩ :=
    finiteDiaryCodeInputs_covers n A DA
  have h : AbsorbsEveryTargetFlipInside
      D.graph C D.bound l := hAbs D hD
  simpa only [hGraph,hBound] using h

end DiaryLeafPriority
end ThreeUniformDiaries
