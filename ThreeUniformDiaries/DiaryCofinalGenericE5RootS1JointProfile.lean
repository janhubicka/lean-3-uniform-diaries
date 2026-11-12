import ThreeUniformDiaries.DiaryStableGenericPairPatternColour
import ThreeUniformDiaries.DiaryFiniteRootGenericMeetProfile

/-!
# Track A: cofinal joint E5 pattern, complete mixed colour, and finite-root S1 profile

Fix an unordered induced copy of the actual enumerated generic
3-hypergraph in genuine leaves of a full RoleDiary target K. Fix
a finite set of genuine old target roots W, not necessarily inside
that generic range, and a prescribed edge/nonedge pattern chi on all
represented old generic leaf pairs below cut B.

The already checked generic finite-pattern theorem gives ONE fixed
complete B-singleton colour whose realizers satisfy the whole E5
pattern cofinally in source indices and target values. The vector
of exact singleton meets with all roots in W takes only FINITELY
many values (every coordinate is bounded by its fixed root).
Ordinary downward finite-choice now gives ONE fixed root-meet
vector occurring together with the SAME E5 pattern and SAME complete
B-colour at arbitrarily large positions.

All profile entries are genuine one-splits strictly below their
roots; this follows from full-diary S1 and eventual target-image
bounds, not from declaring an arbitrary formal profile.

The root profile is existential and is NOT guaranteed to be the
source-required S1 generator image profile or favourable E2 sign.
No E3, numeric future reserve, actual relative successor, fixed
next-leaf image, or countable diary unavoidability follows.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every prescribed finite old E5 pair pattern in an ACTUAL
unordered generic true-leaf range admits ONE complete mixed
singleton colour AND ONE exact finite-root S1 meet profile
cofinally and simultaneously.

The selected S1 vector p is fixed before all source/target
lower bounds N,M, and every p(w) is a true one-split < w.
This is genuine simultaneous finite relative geometry, but
does not assert that p is an arbitrary prescribed profile. -/
theorem RoleDiary.exists_cofinal_generic_E5_pattern_and_finiteRootMeetProfile
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (B : Nat) (chi : Nat → Nat → Bool) :
    ∃ c : Fin B → Fin B → Bool,
      ∃ p : FiniteRootMeetProfile W,
        (∀ w : {w : Nat // w ∈ W},
          IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
        (∀ N M : Nat, ∃ t : Nat,
          N ≤ t ∧ M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
          DiaryLowerBoundColors.singletonColour K B (F t) = c ∧
          (∀ i j : Nat, F i < F j → F j < B →
            (K.edge (F i) (F j) (F t) ↔
              chi (F i) (F j) = true)) ∧
          (∀ w : {w : Nat // w ∈ W},
            K.oneMeetLevel w.val (F t) = (p w).val)) := by
  classical
  obtain ⟨c, hRecur⟩ :=
    exists_cofinal_generic_pair_pattern_full_colour
      G K F hFLeaf B chi
  let T := W.sup (fun w : Nat => w)
  let profile : Nat → FiniteRootMeetProfile W :=
    fun t w => ⟨K.oneMeetLevel w.val (F t), by
      have hCap : K.oneMeetLevel w.val (F t) ≤ w.val :=
        (K.oneMeetLevel_le_min w.val (F t)).trans
          (min_le_left _ _)
      have hw : w.val ≤ T :=
        Finset.le_sup (f := fun x : Nat => x) w.property
      omega⟩
  let R : FiniteRootMeetProfile W → Nat → Prop :=
    fun p N => ∃ t : Nat,
      N ≤ t ∧ N < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
      DiaryLowerBoundColors.singletonColour K B (F t) = c ∧
      (∀ i j : Nat, F i < F j → F j < B →
        (K.edge (F i) (F j) (F t) ↔
          chi (F i) (F j) = true)) ∧
      profile t = p
  have hDown : ∀ p : FiniteRootMeetProfile W,
      ∀ N M : Nat, M ≤ N → R p N → R p M := by
    intro p N M hMN
    rintro ⟨t, htN, hImageN, hB, hLeaf, hColour, hPattern, hp⟩
    exact ⟨t, hMN.trans htN,
      lt_of_le_of_lt hMN hImageN, hB, hLeaf, hColour, hPattern, hp⟩
  have hCover : ∀ N : Nat,
      ∃ p : FiniteRootMeetProfile W,
        p ∈ (Finset.univ : Finset (FiniteRootMeetProfile W)) ∧ R p N := by
    intro N
    obtain ⟨t, htN, hImageN, hB, hLeaf, hColour, hPattern⟩ :=
      hRecur N N
    exact ⟨profile t, Finset.mem_univ _,
      t, htN, hImageN, hB, hLeaf, hColour, hPattern, rfl⟩
  obtain ⟨p, _hp, hAll⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset (FiniteRootMeetProfile W))
      R hDown hCover
  have hRoles (w : {w : Nat // w ∈ W}) :
      IsOneSplit K (p w).val ∧ (p w).val < w.val := by
    obtain ⟨t, _ht, hImage, _hB, hLeaf, _hColour, _hPattern, hProfile⟩ :=
      hAll (T + 1)
    have hwBound : w.val ≤ T :=
      Finset.le_sup (f := fun x : Nat => x) w.property
    have hwLt : w.val < F t := by omega
    have hwLeaf : IsLeaf K w.val := hRoots w.val w.property
    have hNe : w.val ≠ F t := ne_of_lt hwLt
    have hMeet : K.oneMeetLevel w.val (F t) = (p w).val := by
      have h := congrArg (fun z : FiniteRootMeetProfile W => (z w).val)
        hProfile
      change K.oneMeetLevel w.val (F t) = (p w).val at h
      exact h
    have hOne : IsOneSplit K (K.oneMeetLevel w.val (F t)) :=
      DK.singleton_meets w.val (F t) hwLeaf hLeaf hNe
    have hLt : K.oneMeetLevel w.val (F t) < w.val :=
      DK.oneMeet_lt_left_of_distinct_leaves
        w.val (F t) hwLeaf hLeaf hNe
    rw [hMeet] at hOne hLt
    exact ⟨hOne, hLt⟩
  refine ⟨c, p, hRoles, ?_⟩
  intro N M
  obtain ⟨t, ht, hImage, hB, hLeaf, hColour, hPattern, hProfile⟩ :=
    hAll (max N M)
  refine ⟨t, (le_max_left _ _).trans ht,
    lt_of_le_of_lt (le_max_right _ _) hImage,
    hB, hLeaf, hColour, hPattern, ?_⟩
  intro w
  have h := congrArg (fun z : FiniteRootMeetProfile W => (z w).val)
    hProfile
  change K.oneMeetLevel w.val (F t) = (p w).val at h
  exact h

end DiaryLeafPriority
end ThreeUniformDiaries
