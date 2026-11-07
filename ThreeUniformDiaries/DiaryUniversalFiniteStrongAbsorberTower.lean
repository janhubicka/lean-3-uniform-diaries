import ThreeUniformDiaries.DiaryFiniteAbsorberTargetExtension
import ThreeUniformDiaries.DiaryFiniteLeafThreeRigidity

/-!
# Track B: a coherent chain of universal finite strong flip absorbers

The verified target-side extension theorem lets us enlarge ANY finite
full target diary B to a finite full target C with:
  * one BOUNDED, induced, all-numerical-meet embedding B -> C;
  * absorption of EVERY full finite source of a specified frame size
    inside EVERY genuine flip of C.

Iterate this theorem at successively larger finite source sizes.
Unlike independent finite absorbers, the output is an actual
omega-sequence of finite targets with selected transition embeddings.
Composition yields bounded protected embeddings from EVERY earlier
target into EVERY later target; upward closure transports their
strong every-target-flip absorption promises to ALL later levels.

The old target is allowed to MOVE along its selected embedding.
This tower does NOT say that source copies occurring inside the
successive target flips are compatible under restriction. Nor does
it produce a countable full RoleDiary as a literal union, or prove
unrestricted countable-source flip absorption. The finite leaf-three
obstruction prohibits imposing identity-on-initial-segment maps.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every finite diary is boundedly, completely meet-embedded into
itself by the literal identity. -/
theorem FiniteDiaryInput.boundedIdentity
    (B : FiniteDiaryInput) :
    FiniteBoundedMeetEmbedding
      B.graph B.graph B.bound B.bound (fun u => u) := by
  refine ⟨?_, ?_⟩
  · refine {
      strictMono := strictMono_id
      marker_zero := rfl
      marker_one := rfl
      marker_two := rfl
      edge_iff := ?_
      leaf_iff := ?_
      oneSplit_iff := ?_
      twoSplit_iff := ?_
      oneMeet := ?_
      twoMeet := ?_
    }
    · intro a b c hab hbc hcn
      rfl
    · intro u hu3 hun
      rfl
    · intro u hu3 hun
      rfl
    · intro u hu3 hun
      rfl
    · intro u v hu3 hun hv3 hvn
      rfl
    · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
      rfl
  · intro u hu
    exact hu

/-- One explicit selectable successor of a finite target.
The underlying proof is the VERIFIED finite target-extension
strong absorber theorem: no new existence assumption is used. -/
noncomputable def FiniteDiaryInput.nextUniformAbsorber
    (B : FiniteDiaryInput) (n : Nat) :
    { C : FiniteDiaryInput //
      (∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          B.graph C.graph B.bound C.bound f) ∧
      (∀ A : Ordered3Graph Nat,
        FiniteRoleDiaryBlock A n →
          AbsorbsEveryTargetFlipInside
            A C.graph n C.bound) } := by
  classical
  obtain ⟨C,k,DC,hOld,hAll⟩ :=
    exists_finiteDiary_extension_universal_strong_at_size B n
  exact ⟨⟨C,k,DC⟩,hOld,hAll⟩

/-- Genuine finite full target at each stage. The first target
is the verified four-vertex, one-leaf diary. At successor stage
n+1 the new target absorbs EVERY finite full source of size n+4.
No stage is assumed to be a literal initial-segment extension. -/
noncomputable def universalStrongAbsorberTower : Nat → FiniteDiaryInput :=
  Nat.rec
    (⟨finiteEmptyThree,4,finiteEmptyThree_four_is_finiteDiary⟩ :
      FiniteDiaryInput)
    (fun n B => (B.nextUniformAbsorber (n+4)).1)

theorem universalStrongAbsorberTower_succ (n : Nat) :
    universalStrongAbsorberTower (n+1) =
      ((universalStrongAbsorberTower n).nextUniformAbsorber (n+4)).1 := by
  rfl

/-- Each tower transition is a REAL bounded finite meet embedding.
The protected image need NOT fix old ranks. -/
theorem universalStrongAbsorberTower_next_embedding
    (n : Nat) :
    ∃ f : Nat → Nat,
      FiniteBoundedMeetEmbedding
        (universalStrongAbsorberTower n).graph
        (universalStrongAbsorberTower (n+1)).graph
        (universalStrongAbsorberTower n).bound
        (universalStrongAbsorberTower (n+1)).bound f := by
  have h :=
    ((universalStrongAbsorberTower n).nextUniformAbsorber (n+4)).2.1
  simpa only [universalStrongAbsorberTower_succ] using h

/-- At stage n+1 the target absorbs ALL genuine finite full
diaries of source frame n+4, inside EVERY genuine target flip. -/
theorem universalStrongAbsorberTower_next_absorbs
    (n : Nat) :
    ∀ A : Ordered3Graph Nat,
      FiniteRoleDiaryBlock A (n+4) →
        AbsorbsEveryTargetFlipInside
          A (universalStrongAbsorberTower (n+1)).graph
          (n+4) (universalStrongAbsorberTower (n+1)).bound := by
  have h :=
    ((universalStrongAbsorberTower n).nextUniformAbsorber (n+4)).2.2
  simpa only [universalStrongAbsorberTower_succ] using h

/-- Genuine BOUNDED all-meet embeddings from any earlier tower
target into any later one, obtained by composing the already
chosen successor embeddings. -/
theorem universalStrongAbsorberTower_embeds_later
    (i j : Nat) (hij : i ≤ j) :
    ∃ f : Nat → Nat,
      FiniteBoundedMeetEmbedding
        (universalStrongAbsorberTower i).graph
        (universalStrongAbsorberTower j).graph
        (universalStrongAbsorberTower i).bound
        (universalStrongAbsorberTower j).bound f := by
  induction j, hij using Nat.le_induction with
  | base =>
      exact ⟨fun u => u,
        (universalStrongAbsorberTower i).boundedIdentity⟩
  | succ j hij ih =>
      obtain ⟨f,Ef⟩ := ih
      obtain ⟨g,Eg⟩ := universalStrongAbsorberTower_next_embedding j
      refine ⟨fun u => g (f u), ?_⟩
      exact Ef.comp Eg
        (universalStrongAbsorberTower j).diary.prediary.frame.length_ge_three

/-- Every earlier strong absorption guarantee persists through
ALL later target enlargements, for every actual finite target
flip, with the source and target bounds remaining honest. -/
theorem universalStrongAbsorberTower_absorbs_earlier_size
    (i j : Nat) (hij : i+1 ≤ j) :
    ∀ A : Ordered3Graph Nat,
      FiniteRoleDiaryBlock A (i+4) →
        AbsorbsEveryTargetFlipInside
          A (universalStrongAbsorberTower j).graph
          (i+4) (universalStrongAbsorberTower j).bound := by
  intro A DA
  have hAbs :=
    universalStrongAbsorberTower_next_absorbs i A DA
  obtain ⟨f,Ef⟩ :=
    universalStrongAbsorberTower_embeds_later (i+1) j hij
  exact absorbsEveryTargetFlipInside_of_target_embedding
    (universalStrongAbsorberTower (i+1)).diary hAbs Ef


/-- A single sufficiently late tower stage absorbs EVERY full
finite source diary of any specified frame n >= 4, not merely
the exact frame size named when that stage was constructed.
The bound on the target stage j is explicit: j >= n-3.

The result is uniform over ALL finite source edge tables of
this n, inside EVERY genuine target flip. It does NOT pick
compatible source copies for different n. -/
theorem universalStrongAbsorberTower_absorbs_any_finite_size
    (n j : Nat) (hn : 4 ≤ n) (hj : n - 3 ≤ j) :
    ∀ A : Ordered3Graph Nat,
      FiniteRoleDiaryBlock A n →
        AbsorbsEveryTargetFlipInside
          A (universalStrongAbsorberTower j).graph
          n (universalStrongAbsorberTower j).bound := by
  intro A DA
  have hEq : (n - 4) + 4 = n := by omega
  have hLate : (n - 4) + 1 ≤ j := by omega
  have hRaw :=
    universalStrongAbsorberTower_absorbs_earlier_size
      (n - 4) j hLate A
      (by simpa only [hEq] using DA)
  simpa only [hEq] using hRaw


/-- The SAME later target tower stage absorbs an arbitrary prescribed
finite list of source diaries, even when their finite frames have
DIFFERENT sizes (all at least 4). Choose a stage beyond the largest
source frame, then use the verified persistence across the tower.

This is target-side uniformity only. It does not select a compatible
family of source embeddings inside the successive target flips. -/
theorem universalStrongAbsorberTower_eventually_absorbs_finiteFamily
    (Ds : List FiniteDiaryInput)
    (hFour : ∀ D : FiniteDiaryInput, D ∈ Ds → 4 ≤ D.bound) :
    ∃ j : Nat,
      ∀ D : FiniteDiaryInput, D ∈ Ds →
        AbsorbsEveryTargetFlipInside
          D.graph (universalStrongAbsorberTower j).graph
          D.bound (universalStrongAbsorberTower j).bound := by
  classical
  let M : Nat := Ds.toFinset.sup (fun D : FiniteDiaryInput => D.bound)
  refine ⟨M, ?_⟩
  intro D hD
  have hMem : D ∈ Ds.toFinset := by simpa using hD
  have hBound : D.bound ≤ M := Finset.le_sup hMem
  have hLate : D.bound - 3 ≤ M := by omega
  exact universalStrongAbsorberTower_absorbs_any_finite_size
    D.bound M (hFour D hD) hLate D.graph D.diary

end DiaryLeafPriority
end ThreeUniformDiaries
