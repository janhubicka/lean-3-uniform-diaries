import ThreeUniformDiaries.DiaryFiniteCandidatePersistentFusion

/-!
# Track A: eventual stabilization of canonical SOURCE support below any cut

The finite canonical leaf-meet supports S_n form an increasing family.
For any fixed SOURCE numerical cut B, their intersections with [0,B)
eventually stop changing, because only B vertices can ever appear there.
This is a direct finite-choice proof: choose for each eventually occurring
u<B one finite stage at which u appears, and take the maximum of the
finitely many chosen stages.

This removes a misleading possible explanation for next-leaf escape:
infinitely many NEW SOURCE vertices cannot keep being inserted BELOW
one fixed source leaf m.  The theorem DOES NOT bound images of these
source vertices in the TARGET diary, give compatible target maps, or
prove the still-open persistent next-leaf/no-escape theorem.

No RoleDiary or genericity hypothesis is needed for this finite fact.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every FINITELY PERSISTENT reserved old stage has an actual
compatible immediate reserved successor. This is just the horizon-1
case of persistence. In particular the remaining no-escape problem
is not existence of an immediate extension, but selecting an
immediate extension that is ITSELF finitely persistent. -/
theorem PersistentReservedDiaryStage.has_compatible_immediate_successor
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (P : PersistentReservedDiaryStage H K F m f) :
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g :=
  P.2 1


/-- For each fixed source cut B, the finite canonical supports have a
stationary intersection with [0,B) after some finite source horizon.
This is genuine support equality, not a statement about target images. -/
theorem exists_eventually_stable_canonicalSupport_below
    (H : Ordered3Graph Nat) (B : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      (countableDiaryFiniteSupport H n).filter (fun u => u < B) =
      (countableDiaryFiniteSupport H N).filter (fun u => u < B) := by
  classical
  let first : Nat → Nat := fun u =>
    if h : ∃ n : Nat, u ∈ countableDiaryFiniteSupport H n
    then Classical.choose h else 0
  let N : Nat := (Finset.range B).sup first
  refine ⟨N, ?_⟩
  intro n hNn
  apply Finset.ext
  intro u
  constructor
  · intro hu
    obtain ⟨hUn, huB⟩ := Finset.mem_filter.mp hu
    have huExists : ∃ k : Nat, u ∈ countableDiaryFiniteSupport H k :=
      ⟨n, hUn⟩
    have huFirst : u ∈ countableDiaryFiniteSupport H (first u) := by
      dsimp [first]
      rw [dif_pos huExists]
      exact Classical.choose_spec huExists
    have hFirstBound : first u ≤ N := by
      exact Finset.le_sup (f := first)
        (Finset.mem_range.mpr huB)
    have huAtN : u ∈ countableDiaryFiniteSupport H N :=
      countableDiaryFiniteSupport_mono H
        (first u) N hFirstBound huFirst
    exact Finset.mem_filter.mpr ⟨huAtN, huB⟩
  · intro hu
    obtain ⟨huN, huB⟩ := Finset.mem_filter.mp hu
    have huLater : u ∈ countableDiaryFiniteSupport H n :=
      countableDiaryFiniteSupport_mono H N n hNn huN
    exact Finset.mem_filter.mpr ⟨huLater, huB⟩

/-- Specialization to all source coordinates at most a fixed true
source leaf m.  Even if later leaves create old-index meet events,
only finitely many such source positions can ever appear. -/
theorem exists_eventually_stable_canonicalSupport_through
    (H : Ordered3Graph Nat) (m : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      (countableDiaryFiniteSupport H n).filter (fun u => u ≤ m) =
      (countableDiaryFiniteSupport H N).filter (fun u => u ≤ m) := by
  obtain ⟨N, hN⟩ :=
    exists_eventually_stable_canonicalSupport_below H (m + 1)
  refine ⟨N, ?_⟩
  intro n hn
  simpa only [Nat.lt_succ_iff] using hN n hn

end DiaryLeafPriority
end ThreeUniformDiaries
