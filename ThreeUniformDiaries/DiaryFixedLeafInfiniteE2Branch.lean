import ThreeUniformDiaries.DiaryHighTwoSidedE2RangeWitness

/-!
# Track D: infinitely many E2 successors relative to one FIXED target leaf

The high two-sided E2 theorem chooses its split and BOTH leaves
together. A separate finite-preimage argument gives a genuinely
ROOTED, though weaker, positive fact.

Fix ANY real target leaf w=F(i0) of an injective prescribed target
leaf range. For every other leaf v in the range, S1 makes its
numerical singleton meet with w a genuine one-split strictly below
w. There are only FINITELY MANY such possible split indices. Hence
one particular split s<w is witnessed by cofinally many v's beyond
w, even when F is unordered. Recursively select infinitely many
distinct such v's. The V1 witness law forces each v onto the branch
opposite w at that same s.

The OLD LEAF w is now fixed, but s and the E2 sign are NOT
prescribed in advance. No gap bounds or simultaneous E3/E5
constraints, and no persistent relative stage, are obtained.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For every fixed genuine leaf w in an arbitrary injected leaf
range, there is SOME fixed genuine one-split s strictly below w
and an infinite strictly input-increasing sequence of OTHER
range leaves numerically above w whose exact meet with w is s.

All E2 bits E(0,s,w) versus E(0,s,v_k) are literally opposite.
The cut s is chosen after w; it cannot be prescribed as the image
of an already fixed source split. No future-order reserve is
asserted. -/
theorem RoleDiary.fixed_leaf_infinite_constant_E2_branch
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInj : Function.Injective F)
    (hLeaves : ∀ n : Nat, IsLeaf K (F n))
    (i0 N : Nat) :
    ∃ s : Nat,
      IsOneSplit K s ∧ s < F i0 ∧
      ∃ indices : Nat → Nat,
        StrictMono indices ∧
        (∀ k : Nat,
          N ≤ indices k ∧ i0 < indices k ∧
          F i0 < F (indices k) ∧
          K.oneMeetLevel (F i0) (F (indices k)) = s ∧
          ((K.edge 0 s (F i0) ∧ ¬ K.edge 0 s (F (indices k))) ∨
           (¬ K.edge 0 s (F i0) ∧ K.edge 0 s (F (indices k))))) := by
  classical
  let w := F i0
  obtain ⟨M,hLarge⟩ := injective_nat_eventually_above_bound F hInj w
  let base := max (max N (i0 + 1)) M
  have hAfter (n : Nat) : i0 < base + n := by
    dsimp [base]
    omega
  have hNumerical (n : Nat) : w < F (base + n) := by
    apply hLarge (base + n)
    dsimp [base]
    omega
  have hDistinct (n : Nat) : w ≠ F (base + n) := by
    intro h
    have hEq : i0 = base + n := hInj h
    have hI := hAfter n
    omega
  have hSplit (n : Nat) :
      IsOneSplit K (K.oneMeetLevel w (F (base + n))) :=
    DK.singleton_meets w (F (base + n))
      (hLeaves i0) (hLeaves (base + n)) (hDistinct n)
  have hMeetLt (n : Nat) :
      K.oneMeetLevel w (F (base + n)) < w := by
    have hCap :
        K.oneMeetLevel w (F (base + n)) ≤ w :=
      (K.oneMeetLevel_le_min w (F (base + n))).trans
        (min_le_left _ _)
    have hNe : K.oneMeetLevel w (F (base + n)) ≠ w := by
      intro hEq
      have hBad : IsOneSplit K w := hEq ▸ hSplit n
      exact (hLeaves i0).2.1 hBad.2.1
    omega
  let R : Nat → Nat → Prop := fun s q =>
    ∃ n : Nat, q ≤ n ∧
      K.oneMeetLevel w (F (base + n)) = s
  have hDown : ∀ (s : Nat) (q p : Nat),
      p ≤ q → R s q → R s p := by
    intro s q p hpq
    rintro ⟨n, hqn, hAt⟩
    exact ⟨n, hpq.trans hqn, hAt⟩
  have hCover : ∀ q : Nat,
      ∃ s : Nat, s ∈ Finset.range w ∧ R s q := by
    intro q
    exact ⟨K.oneMeetLevel w (F (base + q)),
      Finset.mem_range.mpr (hMeetLt q),
      q, le_rfl, rfl⟩
  obtain ⟨s, _hIn, hRec⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.range w) R hDown hCover
  let pick : Nat → Nat := fun q => Classical.choose (hRec q)
  have hPick (q : Nat) :
      q ≤ pick q ∧
      K.oneMeetLevel w (F (base + pick q)) = s := by
    exact Classical.choose_spec (hRec q)
  let pos : Nat → Nat :=
    Nat.rec (pick 0) (fun _ prev => pick (prev + 1))
  have hPosStep (k : Nat) : pos k < pos (k + 1) := by
    change pos k < pick (pos k + 1)
    have h := (hPick (pos k + 1)).1
    omega
  have hPosMono : StrictMono pos :=
    strictMono_nat_of_lt_succ hPosStep
  let indices : Nat → Nat := fun k => base + pos k
  have hIndicesMono : StrictMono indices := by
    intro i j hij
    have h := hPosMono hij
    dsimp [indices]
    omega
  have hSameMeet (k : Nat) :
      K.oneMeetLevel w (F (indices k)) = s := by
    cases k with
    | zero =>
        change K.oneMeetLevel w (F (base + pick 0)) = s
        exact (hPick 0).2
    | succ k =>
        change K.oneMeetLevel w
          (F (base + pick (pos k + 1))) = s
        exact (hPick (pos k + 1)).2
  have hs : IsOneSplit K s := by
    have h := hSplit (pos 0)
    rw [hSameMeet 0] at h
    exact h
  have hsBelow : s < w := by
    have h := hMeetLt (pos 0)
    rw [hSameMeet 0] at h
    exact h
  refine ⟨s,hs,hsBelow,indices,hIndicesMono,?_⟩
  intro k
  have hN : N ≤ indices k := by
    dsimp [indices,base]
    omega
  have hI : i0 < indices k := hAfter (pos k)
  have hW : w < F (indices k) := hNumerical (pos k)
  have hMeet := hSameMeet k
  have hOpp :
      ¬ (K.edge 0 s w ↔ K.edge 0 s (F (indices k))) :=
    DK.oneSplit_witness_opposite_marker
      s w (F (indices k)) hs
      (hLeaves i0) (hLeaves (indices k))
      hsBelow (lt_trans hsBelow hW) hMeet
  refine ⟨hN,hI,hW,hMeet,?_⟩
  tauto

end DiaryLeafPriority
end ThreeUniformDiaries
