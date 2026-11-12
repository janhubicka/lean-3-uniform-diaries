import ThreeUniformDiaries.DiarySelectedAbsorberProtectedReserve

/-!
# Track B: a protected finite absorber tower requires a permanent free tail

Under a hypothetical protected reserve on the ACTUAL unbounded selected
strong-absorber tower, EVERY finite full target stage must contain at
least one vertex strictly beyond its protected cut. This holds even at
stages where the immediate successor does not enlarge the frame.

If one entire finite full diary were ever protected literally, the
nondecreasing future cuts would fix its entire frame under ALL future
selected embeddings. Since the target finite frames are unbounded,
that would give a proper literal full-diary extension, contradicting
the already verified finite no-end-extension theorem.

The terminal vertex of each genuine finite full diary is a LEAF.
Consequently the next target stage has a genuine terminal leaf beyond
every old selected image, ready to play the role of an unfrozen tail
buffer. This is a necessary invariant only; it does NOT construct a
tower with a protected reserve or prove countable flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace SelectedAbsorberProtectedReserve

/-- Every protected cut of a hypothetical *unbounded* selected
strong-absorber tower is PROPER, even if the next transition happens
to have equal frame size. An entire full finite diary can never
be protected permanently through the whole future tower. -/
theorem cut_strict_every_stage
    {r : Nat → Nat} (H : SelectedAbsorberProtectedReserve r)
    (n : Nat) :
    r n < (universalStrongAbsorberTower n).bound := by
  have hWithin := H.within_frame n
  by_contra hNot
  have hEq : r n = (universalStrongAbsorberTower n).bound := by
    omega
  have hForwardFixed : ∀ k u : Nat,
      u < (universalStrongAbsorberTower n).bound →
      universalStrongAbsorberTower_forwardMap n k u = u := by
    intro k
    induction k with
    | zero =>
        intro u hu
        rfl
    | succ k ih =>
        intro u hu
        have hCut : u < r (n+k) := by
          have hMono : r n ≤ r (n+k) :=
            H.monotone_cut (by omega)
          omega
        calc
          universalStrongAbsorberTower_forwardMap n (k+1) u =
              universalStrongAbsorberTower_stepMap (n+k)
                (universalStrongAbsorberTower_forwardMap n k u) := rfl
          _ = universalStrongAbsorberTower_stepMap (n+k) u := by
            rw [ih u hu]
          _ = u := H.fixes_cut (n+k) u hCut
  obtain ⟨j,hBig⟩ :=
    universalStrongAbsorberTower_unbounded_frame
      (universalStrongAbsorberTower n).bound
  have hnj : n ≤ j := by
    by_contra h
    have hjle : j ≤ n := by omega
    have hSizes :=
      selectedAbsorberFiniteOrderTower.size_mono j n hjle
    have hBound :
        (universalStrongAbsorberTower j).bound ≤
          (universalStrongAbsorberTower n).bound := by
      simpa only [selectedAbsorberFiniteOrderTower] using hSizes
    omega
  let k : Nat := j-n
  have hIdx : n+k = j := by
    dsimp [k]
    omega
  have hGrow :
      (universalStrongAbsorberTower n).bound <
        (universalStrongAbsorberTower (n+k)).bound := by
    rw [hIdx]
    exact hBig
  have hFour : 4 ≤ (universalStrongAbsorberTower n).bound := by
    have hSize :=
      selectedAbsorberFiniteOrderTower.size_mono 0 n (Nat.zero_le n)
    change 4 ≤ (universalStrongAbsorberTower n).bound at hSize
    exact hSize
  obtain ⟨u,hu,hMove⟩ :=
    finiteFullDiary_properEmbedding_moves_old_rank
      (universalStrongAbsorberTower n).diary
      (universalStrongAbsorberTower (n+k)).diary
      hFour hGrow (universalStrongAbsorberTower_forwardMap_spec n k)
  exact hMove (hForwardFixed k u hu)

/-- At every successor stage, the last vertex of the next
genuine finite full diary is a LEAF, strictly outside the image
of EVERY vertex of the previous selected full finite diary.
The reserve must always leave an unfrozen terminal witness. -/
theorem has_unused_terminal_leaf_after_step
    {r : Nat → Nat} (H : SelectedAbsorberProtectedReserve r)
    (n : Nat) :
    ∃ v : Nat,
      v < (universalStrongAbsorberTower (n+1)).bound ∧
      IsLeaf (universalStrongAbsorberTower (n+1)).graph v ∧
      (∀ u : Nat, u < (universalStrongAbsorberTower n).bound →
        universalStrongAbsorberTower_stepMap n u < v) := by
  let v : Nat := (universalStrongAbsorberTower (n+1)).bound - 1
  have hFour : 4 ≤ (universalStrongAbsorberTower (n+1)).bound := by
    have hSize :=
      selectedAbsorberFiniteOrderTower.size_mono 0 (n+1)
        (Nat.zero_le (n+1))
    change 4 ≤ (universalStrongAbsorberTower (n+1)).bound at hSize
    exact hSize
  have hv : v < (universalStrongAbsorberTower (n+1)).bound := by
    dsimp [v]
    omega
  have hLeaf : IsLeaf (universalStrongAbsorberTower (n+1)).graph v := by
    exact (universalStrongAbsorberTower (n+1)).diary.last_is_leaf hFour
  refine ⟨v,hv,hLeaf,?_⟩
  intro u hu
  have hReserve := H.reserves_old_images n u hu
  have hStrict := H.cut_strict_every_stage (n+1)
  dsimp [v]
  omega

end SelectedAbsorberProtectedReserve
end DiaryLeafPriority
end ThreeUniformDiaries
