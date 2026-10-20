import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection
import ThreeUniformDiaries.DiaryFiniteFamilyFiniteTarget
import ThreeUniformDiaries.DiaryFiniteSupportInverseRank

/-!
# A range-correct finite embedding interface and bounded universality

The historical FiniteMeetEmbedding API is a total map Nat → Nat
whose finite source diagram is [0,n). It checks all edges/nonedges,
roles, and all numerical singleton/full pair meets, but does NOT
require that the original n source vertices land in the target
finite frame [0,k). The latter is essential when using the
embedding under a later target flip, whose invariants only hold
inside that finite frame.

We state the honest bounded target interface, and strengthen the
finite-family and fixed-size universal diary results. No new
mathematical assumption is needed: the verified finite-support
compression already maps each source vertex to a rank < S.card.
The existing theorem simply did not EXPORT that bound.

The stronger finite absorption predicate also requires finite
ranges. This is a definition, NOT a proof of absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- An exact finite meet embedding with every genuine finite
source vertex landing INSIDE the target bounded finite diary. -/
structure FiniteBoundedMeetEmbedding
    (A T : Ordered3Graph Nat) (n k : Nat) (f : Nat → Nat) : Prop where
  toMeetEmbedding : FiniteMeetEmbedding A T n f
  image_bound : ∀ u : Nat, u < n → f u < k

/-- A finite-family joint-embedding theorem with explicitly
bounded copies, not merely maps into the ambient Nat carrier. -/
theorem exists_finiteDiary_for_finiteFamily_bounded
    (Ds : List FiniteDiaryInput) :
    ∃ (T : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock T k ∧
      ∀ D : FiniteDiaryInput, D ∈ Ds →
        ∃ f : Nat → Nat,
          FiniteBoundedMeetEmbedding D.graph T D.bound k f := by
  classical
  obtain ⟨G,DG,hCopies⟩ :=
    exists_countableDiary_for_finiteFamily Ds
  obtain ⟨L,hLeaves,hWitnesses⟩ :=
    exists_finiteFamily_leaf_support (G := G) Ds hCopies
  let S := finiteLeafMeetSupport G L
  let T := finiteSupportGraph G S
  refine ⟨T,S.card,finiteLeafMeetSupport_is_finiteDiary DG hLeaves,?_⟩
  intro D hD
  obtain ⟨f,E,hImageLeaves⟩ := hWitnesses D hD
  have hRange : ∀ u : Nat, u < D.bound → f u ∈ S :=
    FiniteMeetEmbedding.range_subset_leafMeetSupport
      D.diary E L hImageLeaves
  refine ⟨finiteSupportLift S D.bound f, ?_⟩
  refine ⟨(FiniteMeetEmbedding.factor_through_leafMeetSupport
    D.diary DG E L hLeaves hImageLeaves).2, ?_⟩
  intro u hu
  exact (finiteSupportLift_spec S D.bound f hRange u hu).1

/-- Every finite diary of a given size embeds into one genuine
FINITE diary, and all selected copy vertices actually lie below
the target's finite bound k. -/
theorem exists_finiteDiary_universal_bound_bounded
    (n : Nat) :
    ∃ (T : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock T k ∧
      ∀ (A : Ordered3Graph Nat), FiniteRoleDiaryBlock A n →
        ∃ f : Nat → Nat,
          FiniteBoundedMeetEmbedding A T n k f := by
  classical
  obtain ⟨T,k,DT,hCopies⟩ :=
    exists_finiteDiary_for_finiteFamily_bounded
      (finiteDiaryCodeInputs n)
  refine ⟨T,k,DT,?_⟩
  intro A DA
  obtain ⟨D,hD,hGraph,hBound⟩ :=
    finiteDiaryCodeInputs_covers n A DA
  obtain ⟨f,hEmbedding⟩ := hCopies D hD
  refine ⟨f, ?_⟩
  simpa only [hGraph,hBound] using hEmbedding

/-- Strengthened FIRST flip direction: every source flip embeds
INSIDE the same bounded target diary, not in its artificial tail.
This still does not establish every-target-flip absorption. -/
theorem exists_finiteDiary_for_all_source_flips_bounded
    (A : Ordered3Graph Nat) (n : Nat)
    (_DA : FiniteRoleDiaryBlock A n) :
    ∃ (B : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock B k ∧
      ∀ A' : Ordered3Graph Nat, FiniteDiaryFlip A A' n →
        ∃ f : Nat → Nat,
          FiniteBoundedMeetEmbedding A' B n k f := by
  obtain ⟨B,k,DB,hUniversal⟩ :=
    exists_finiteDiary_universal_bound_bounded n
  refine ⟨B,k,DB,?_⟩
  intro A' hFlip
  exact hUniversal A' hFlip.target_diary

/-- The exact unproved finite absorption goal WITH an explicit
finite target range. Unlike the old range-free predicate, this
cannot use the artificial infinite Nat tail as a source image. -/
def AbsorbsEveryTargetFlipInside
    (A B : Ordered3Graph Nat) (n k : Nat) : Prop :=
  ∀ B' : Ordered3Graph Nat,
    FiniteDiaryFlip B B' k →
      ∃ f : Nat → Nat, FiniteBoundedMeetEmbedding A B' n k f

/-- The corrected absorption property implies the historical
range-free property. The converse is not assumed or asserted. -/
theorem absorbsEveryTargetFlip_of_inside
    {A B : Ordered3Graph Nat} {n k : Nat}
    (h : AbsorbsEveryTargetFlipInside A B n k) :
    AbsorbsEveryTargetFlip A B n k := by
  intro B' F
  obtain ⟨f,E⟩ := h B' F
  exact ⟨f,E.toMeetEmbedding⟩

end DiaryLeafPriority
end ThreeUniformDiaries
