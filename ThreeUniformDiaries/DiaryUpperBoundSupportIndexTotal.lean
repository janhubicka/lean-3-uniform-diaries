import ThreeUniformDiaries.DiaryFiniteLeafMeetS1Reduct

/-!
# Track A: strictly increasing total extension of a finite diary support enumeration

A finite support S is enumerated in its original order by
finiteSupportIndex S : Nat → Nat, but that map returns ZERO outside
[0,S.card) and is therefore NOT globally strictly increasing.

FiniteAuxEmbedding and FiniteLeafPreembedding require a total
strictly increasing Nat-map, though their mathematical constraints
only inspect the genuine finite source frame. We use the same
consecutive-tail idea as FiniteAuxLocalEmbedding.extend, applied
here to the actual finite support enumeration.

No edge or type condition is imposed on the invented tail.
This lemma must not be confused with an infinite diary embedding.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The increasing enumeration of S below its size, continued
consecutively after the last enumerated element. For S=empty,
the total extension is the identity. -/
noncomputable def finiteSupportIndexTotal
    (S : Finset Nat) (i : Nat) : Nat :=
  if hi : i < S.card then finiteSupportIndex S i
  else finiteSupportIndex S (S.card - 1) + (i - (S.card - 1))

/-- This total extension agrees LITERALLY with the original
finite support enumeration at every genuine finite index. -/
theorem finiteSupportIndexTotal_inside
    (S : Finset Nat) (i : Nat) (hi : i < S.card) :
    finiteSupportIndexTotal S i = finiteSupportIndex S i := by
  simp only [finiteSupportIndexTotal, dif_pos hi]

/-- The total continuation is strictly increasing on all Nat.
The proof uses only finite index ordering and the final image;
no diary or genericity assumptions are needed. -/
theorem finiteSupportIndexTotal_strictMono
    (S : Finset Nat) : StrictMono (finiteSupportIndexTotal S) := by
  intro i j hij
  by_cases hi : i < S.card
  · by_cases hj : j < S.card
    · rw [finiteSupportIndexTotal_inside S i hi,
          finiteSupportIndexTotal_inside S j hj]
      exact finiteSupportIndex_strictMono S i j hij hj
    · have hlast : S.card - 1 < S.card := by omega
      have hle :
          finiteSupportIndex S i ≤
            finiteSupportIndex S (S.card - 1) :=
        finiteSupportIndex_mono_below S i (S.card - 1)
          hi hlast (by omega)
      rw [finiteSupportIndexTotal_inside S i hi]
      simp only [finiteSupportIndexTotal, dif_neg hj]
      omega
  · have hj : ¬ j < S.card := by omega
    simp only [finiteSupportIndexTotal, dif_neg hi, dif_neg hj]
    omega

/-- If S contains 0,1,2 then its total extension fixes those
three markers, since the finite enumeration already fixes them. -/
theorem finiteSupportIndexTotal_initial_markers
    (S : Finset Nat) (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S) :
    finiteSupportIndexTotal S 0 = 0 ∧
    finiteSupportIndexTotal S 1 = 1 ∧
    finiteSupportIndexTotal S 2 = 2 := by
  obtain ⟨hcard,hZero,hOne,hTwo⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  constructor
  · rw [finiteSupportIndexTotal_inside S 0 (by omega)]
    exact hZero
  constructor
  · rw [finiteSupportIndexTotal_inside S 1 (by omega)]
    exact hOne
  · rw [finiteSupportIndexTotal_inside S 2 (by omega)]
    exact hTwo

/-- Every actual finite support vertex lies BEFORE the first new
tail image. This gives the image-bound hypothesis of a finite
diary leaf preembedding without any max/sup selection. -/
theorem finiteSupportIndexTotal_below_tail
    (S : Finset Nat) (i : Nat) (hi : i < S.card) :
    finiteSupportIndexTotal S i < finiteSupportIndexTotal S S.card :=
  finiteSupportIndexTotal_strictMono S hi

end DiaryLeafPriority
end ThreeUniformDiaries
