import ThreeUniformDiaries.DiaryFiniteInducedMeetsIntoCountable
import ThreeUniformDiaries.DiaryFiniteATRFromExactMeets

/-!
# Track A: finite induced leaf preembeddings preserve ALL nonmarker auxiliary meets

A genuine finite full diary A may be mapped into a countable RoleDiary T
by a finite leaf preembedding P whose source *entire* finite edge/nonedge
table is induced. Its full leaf singleton and pair meets are preserved,
and the E-only mixed-pair marker dichotomy gives mixed auxiliary meets.

The remaining leaf/leaf auxiliary case is obtained directly from the
finite S1/S2 axioms and the existing leaf-pair split-priority algebra.
This is the FINITE analogue of the global RoleDiaryMeets leaf transfer,
without falsely assuming the zero-extended finite source is a global
RoleDiary.

Consequently ALL auxiliary pair meets whose first vertices are
nonmarkers are preserved across arbitrary skipped target levels.

This is a genuine reusable input to upper-bound ATR factorisation.
It is not yet a complete FiniteAuxEmbedding: tests with marker
endpoints must still be checked separately, and the concrete
leaf-support enumeration must be made into an induced leaf
preembedding. No diary Ramsey/unavoidability is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A T : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}

/-- In a bounded full finite diary, the singleton meet of TWO
genuine bounded leaves is strictly after marker 1 and is never a
genuine two-split. This includes repeated coordinates and
the order-reversed case. -/
theorem FiniteRoleDiaryBlock.leaf_coordinate_meet_not_twoSplit
    (DA : FiniteRoleDiaryBlock A n)
    (u v : Nat) (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v) :
    1 < A.oneMeetLevel u v ∧
      ¬ IsTwoSplit A (A.oneMeetLevel u v) := by
  by_cases heq : u = v
  · subst v
    have hself : A.oneMeetLevel u u = u := by
      classical
      have hbound : A.oneMeetLevel u u ≤ u := by
        simpa only [min_self] using A.oneMeetLevel_le_min u u
      have hagree : A.SameOneTypeBelow u u u := by
        intro a b hab hb
        exact Iff.rfl
      have hbelow : u ≤ A.oneMeetLevel u u :=
        Nat.le_findGreatest (by simp) hagree
      exact Nat.le_antisymm hbound hbelow
    rw [hself]
    refine ⟨by have hu3 := hu.1; omega, ?_⟩
    intro hTwo
    exact hu.2.2 hTwo.2.2
  · have hSplit : IsOneSplit A (A.oneMeetLevel u v) :=
      finiteRoleDiary_s1_unordered DA u v hun hvn hu hv heq
    refine ⟨by have hm3 := hSplit.1; omega, ?_⟩
    intro hTwo
    exact hTwo.2.1 hSplit.2.1

/-- Full auxiliary meet transport for two increasing nonmarker
pairs, including ALL leaf/leaf, split/leaf, split/split and
repeated-first-coordinate cases. No convexity of the image
is assumed and all source bounds are literal. -/
theorem FiniteLeafPreembedding.auxMeet_nonmarker_of_induced
    (DA : FiniteRoleDiaryBlock A n)
    (DT : RoleDiary T)
    (P : FiniteLeafPreembedding A T n k f)
    (hInduced : ∀ u v w : Nat, u < v → v < w → w < n →
      (T.edge (f u) (f v) (f w) ↔ A.edge u v w))
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (han : a < n) (hbn : b < n)
    (hc3 : 3 ≤ c) (hcn : c < n) (hdn : d < n) :
    T.auxMeetLevel (f a) (f b) (f c) (f d) =
      f (A.auxMeetLevel a b c d) := by
  have hb3 : 3 ≤ b := by omega
  have hd3 : 3 ≤ d := by omega
  by_cases hAllLeaves :
      (IsLeaf A a ∧ IsLeaf A b) ∧
      (IsLeaf A c ∧ IsLeaf A d)
  · have haLeaf := hAllLeaves.1.1
    have hbLeaf := hAllLeaves.1.2
    have hcLeaf := hAllLeaves.2.1
    have hdLeaf := hAllLeaves.2.2
    obtain ⟨hfirst, hfirstNotTwo⟩ :=
      DA.leaf_coordinate_meet_not_twoSplit
        a c han hcn haLeaf hcLeaf
    obtain ⟨hsecond, hsecondNotTwo⟩ :=
      DA.leaf_coordinate_meet_not_twoSplit
        b d hbn hdn hbLeaf hdLeaf
    exact auxMeetLevel_preserved_of_diary_cases
      A T a b c d hab hcd (IsTwoSplit A)
      (DA.pair_meets a b c d
        hab hcd hbn hdn haLeaf hbLeaf hcLeaf hdLeaf)
      hfirst hsecond hfirstNotTwo hsecondNotTwo
      f P.strictMono
      (P.leaf_twoMeet a b c d hab hcd
        ha3 han hb3 hbn hc3 hcn hd3 hdn
        haLeaf hbLeaf hcLeaf hdLeaf)
      (P.leaf_oneMeet a c ha3 han hc3 hcn haLeaf hcLeaf)
      (P.leaf_oneMeet b d hb3 hbn hd3 hdn hbLeaf hdLeaf)
  · have hSomeSplit :
        (IsDiarySplit A a ∨ IsDiarySplit A b) ∨
        (IsDiarySplit A c ∨ IsDiarySplit A d) := by
      by_cases hAB : IsLeaf A a ∧ IsLeaf A b
      · have hCD : ¬ (IsLeaf A c ∧ IsLeaf A d) := by
          intro hc
          exact hAllLeaves ⟨hAB, hc⟩
        exact Or.inr
          (DA.prediary.pair_contains_split_of_not_both_leaf
            c d hc3 hcn hd3 hdn hCD)
      · exact Or.inl
          (DA.prediary.pair_contains_split_of_not_both_leaf
            a b ha3 han hb3 hbn hAB)
    exact finite_induced_mixed_auxMeet_in_countable
      DA.prediary DT P hInduced a b c d hab hcd
      ha3 han hbn hc3 hcn hdn hSomeSplit

end DiaryLeafPriority
end ThreeUniformDiaries
