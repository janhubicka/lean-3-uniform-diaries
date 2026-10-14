import ThreeUniformDiaries.TwoTypeMeetLevel
import ThreeUniformDiaries.DiaryGappySourceI2Transfer

/-!
# Full 2-type witness independence for diary pre-embeddings

The two-split case of the diary pre-embedding assigns the image of
a source 2-split i by taking the target full 2-type meet of two
ordered pairs of leaves witnessing that split.

The central independence argument is a finite type fact:
if pairs A,A' have the same full 2-type through M+1, then any
other pair B whose meet with A has already occurred by M has the
same meet with A'. Replacing both members of two witness pairs
therefore leaves their target meet unchanged.

This file proves the elementwise lemma for arbitrary enumerated
3-hypergraphs. It is independent of diary role axioms, genericity,
or Ramsey theory. Applying it to the actual fused diary embedding
requires the native I3 conclusion and an upper bound on the first
target pair-meet disagreement at the source 2-split i; those are
the separately tracked pre-embedding proof obligations.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Full 2-type equivalence is symmetric. -/
theorem sameTwoTypeBelow_symm
    (H : Ordered3Graph Nat) (l a b c d : Nat)
    (h : H.SameTwoTypeBelow l a b c d) :
    H.SameTwoTypeBelow l c d a b := by
  rcases h with ⟨h₀, h₁, haux⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    exact (h₀ hxy hy).symm
  · intro x y hxy hy
    exact (h₁ hxy hy).symm
  · intro x hx
    exact (haux (a := x) hx).symm

/-- Full 2-type equivalence is transitive at each fixed cut. -/
theorem sameTwoTypeBelow_trans
    (H : Ordered3Graph Nat)
    (l a b c d e f : Nat)
    (h₀ : H.SameTwoTypeBelow l a b c d)
    (h₁ : H.SameTwoTypeBelow l c d e f) :
    H.SameTwoTypeBelow l a b e f := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    exact (h₀.1 hxy hy).trans (h₁.1 hxy hy)
  · intro x y hxy hy
    exact (h₀.2.1 hxy hy).trans (h₁.2.1 hxy hy)
  · intro x hx
    exact (h₀.2.2 (a := x) hx).trans
      (h₁.2.2 (a := x) hx)

/-- Full 2-type agreement at a cut also holds at every smaller cut. -/
theorem sameTwoTypeBelow_mono
    (H : Ordered3Graph Nat)
    (l m a b c d : Nat) (hlm : l ≤ m)
    (h : H.SameTwoTypeBelow m a b c d) :
    H.SameTwoTypeBelow l a b c d := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    exact h.1 hxy (lt_of_lt_of_le hy hlm)
  · intro x y hxy hy
    exact h.2.1 hxy (lt_of_lt_of_le hy hlm)
  · intro x hx
    exact h.2.2 (a := x) (lt_of_lt_of_le hx hlm)

/-- The full capped pair meet is at least the cut l precisely when
the two full pair types agree below l, provided l lies before both
first coordinates. -/
theorem twoMeetLevel_ge_iff_sameTwoTypeBelow
    (H : Ordered3Graph Nat)
    (l a b c d : Nat) (hla : l ≤ a) (hlc : l ≤ c) :
    l ≤ H.twoMeetLevel a b c d ↔
      H.SameTwoTypeBelow l a b c d := by
  classical
  constructor
  · intro hle
    exact H.sameTwoTypeBelow_mono l
      (H.twoMeetLevel a b c d) a b c d hle
      (H.twoMeetLevel_agree a b c d)
  · intro htype
    exact Nat.le_findGreatest (le_min hla hlc) htype

/-- The capped full two-type meet is symmetric in its two
ordered-pair arguments. -/
theorem twoMeetLevel_comm
    (H : Ordered3Graph Nat) (a b c d : Nat) :
    H.twoMeetLevel a b c d = H.twoMeetLevel c d a b := by
  classical
  have hfun :
      (fun l => H.SameTwoTypeBelow l a b c d) =
      (fun l => H.SameTwoTypeBelow l c d a b) := by
    funext l
    apply propext
    constructor
    · exact H.sameTwoTypeBelow_symm l a b c d
    · exact H.sameTwoTypeBelow_symm l c d a b
  change
    Nat.findGreatest (fun l => H.SameTwoTypeBelow l a b c d) (min a c) =
    Nat.findGreatest (fun l => H.SameTwoTypeBelow l c d a b) (min c a)
  rw [hfun, min_comm a c]

/-- Replacing one pair A by a pair A' of the same full 2-type
through M+1 does not change an earlier pair meet with B. -/
theorem twoMeetLevel_stable_under_close_two_types
    (H : Ordered3Graph Nat)
    (M a b c d a' b' : Nat)
    (hMa : M < a) (hMc : M < c) (hMa' : M < a')
    (hSame : H.SameTwoTypeBelow (M+1) a b a' b')
    (hEarly : H.twoMeetLevel a b c d ≤ M) :
    H.twoMeetLevel a' b' c d =
      H.twoMeetLevel a b c d := by
  let w := H.twoMeetLevel a b c d
  have hwM : w ≤ M := hEarly
  have hAtW : H.SameTwoTypeBelow w a b c d :=
    H.twoMeetLevel_agree a b c d
  have hSameW : H.SameTwoTypeBelow w a b a' b' :=
    H.sameTwoTypeBelow_mono w (M+1) a b a' b'
      (by omega) hSame
  have hAtW' : H.SameTwoTypeBelow w a' b' c d :=
    H.sameTwoTypeBelow_trans w a' b' a b c d
      (H.sameTwoTypeBelow_symm w a b a' b' hSameW) hAtW
  have hLower : w ≤ H.twoMeetLevel a' b' c d :=
    (H.twoMeetLevel_ge_iff_sameTwoTypeBelow
      w a' b' c d (by omega) (by omega)).mpr hAtW'
  have hFail : ¬ H.SameTwoTypeBelow (w+1) a b c d := by
    intro hnext
    have hupper : w+1 ≤ H.twoMeetLevel a b c d :=
      (H.twoMeetLevel_ge_iff_sameTwoTypeBelow
        (w+1) a b c d (by omega) (by omega)).mpr hnext
    omega
  have hSameNext : H.SameTwoTypeBelow (w+1) a b a' b' :=
    H.sameTwoTypeBelow_mono (w+1) (M+1) a b a' b'
      (by omega) hSame
  have hUpper : H.twoMeetLevel a' b' c d ≤ w := by
    by_contra hn
    have hgt : w < H.twoMeetLevel a' b' c d := by omega
    have hAtNext : H.SameTwoTypeBelow (w+1) a' b' c d :=
      H.sameTwoTypeBelow_mono (w+1)
        (H.twoMeetLevel a' b' c d) a' b' c d
        (by omega) (H.twoMeetLevel_agree a' b' c d)
    have hOldNext : H.SameTwoTypeBelow (w+1) a b c d :=
      H.sameTwoTypeBelow_trans (w+1) a b a' b' c d
        hSameNext hAtNext
    exact hFail hOldNext
  exact Nat.le_antisymm hUpper hLower

/-- Replacing BOTH pairs in a witness comparison by pairs of
their respective full 2-type classes leaves the early pair meet
unchanged. This is the two-split witness-independence calculation
needed before constructing a diary pre-embedding. -/
theorem twoMeetLevel_pairWitness_independent
    (H : Ordered3Graph Nat)
    (M a b c d a' b' c' d' : Nat)
    (hMa : M < a) (hMc : M < c)
    (hMa' : M < a') (hMc' : M < c')
    (hSameA : H.SameTwoTypeBelow (M+1) a b a' b')
    (hSameB : H.SameTwoTypeBelow (M+1) c d c' d')
    (hEarly : H.twoMeetLevel a b c d ≤ M) :
    H.twoMeetLevel a' b' c' d' =
      H.twoMeetLevel a b c d := by
  have hFirst : H.twoMeetLevel a' b' c d =
      H.twoMeetLevel a b c d :=
    H.twoMeetLevel_stable_under_close_two_types
      M a b c d a' b' hMa hMc hMa' hSameA hEarly
  have hEarly' : H.twoMeetLevel c d a' b' ≤ M := by
    rw [H.twoMeetLevel_comm c d a' b', hFirst]
    exact hEarly
  have hSecond : H.twoMeetLevel c' d' a' b' =
      H.twoMeetLevel c d a' b' :=
    H.twoMeetLevel_stable_under_close_two_types
      M c d a' b' c' d' hMc hMa' hMc' hSameB hEarly'
  calc
    H.twoMeetLevel a' b' c' d' =
      H.twoMeetLevel c' d' a' b' :=
        H.twoMeetLevel_comm a' b' c' d'
    _ = H.twoMeetLevel c d a' b' := hSecond
    _ = H.twoMeetLevel a' b' c d :=
        H.twoMeetLevel_comm c d a' b'
    _ = H.twoMeetLevel a b c d := hFirst

end Ordered3Graph
end ThreeUniformDiaries
