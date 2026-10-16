import ThreeUniformDiaries.DiaryOnePassRawEdgeShapes

/-!
# Reflect the actual selected-class tests in the one-pass target

Previous modules construct the target relation and prove that a selected
germ gives the intended positive edge. Here we prove the CONVERSE.

First, event positions are globally unique: two events in distinct old
cut blocks cannot share a target vertex; within a block, positions
determine their Fin indices.

It follows that an edge (0, event, f(u)) at a selected singleton event
comes ONLY from that event, and exactly when the old source leaf u has
its selected finite one-germ. Likewise an edge (event, f(u), f(v)) at
a pair event comes exactly from the chosen source full pair-germ.

In particular no off-block event can introduce spurious incidences on
the protected original leaves or leaf pairs. These are genuine target
edge-reflection results, not just positive-incidence implications.

The global original-cut 1/2-type transport induction, V3, S1/S2 and
protected mixed meets remain open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- Different old cuts have disjoint and strictly ordered event blocks. -/
theorem onePassEventPosition_lt_of_cut_lt
    (H : Ordered3Graph Nat) (m n : Nat)
    (i : Fin (onePassBlock H m).length)
    (j : Fin (onePassBlock H n).length)
    (hmn : m < n) :
    onePassEventPosition H m i < onePassEventPosition H n j := by
  have hi := (onePassEventPosition_interval H m i).2
  have hj := (onePassEventPosition_interval H n j).1
  have hsep := onePassOldImage_lt_before H m n hmn
  omega

/-- The position of a fresh event determines its ORIGINAL cut. -/
theorem onePassEventPosition_eq_cut
    (H : Ordered3Graph Nat) (m n : Nat)
    (i : Fin (onePassBlock H m).length)
    (j : Fin (onePassBlock H n).length)
    (h : onePassEventPosition H m i =
      onePassEventPosition H n j) : m = n := by
  by_cases hmn : m < n
  · have hlt := onePassEventPosition_lt_of_cut_lt H m n i j hmn
    omega
  by_cases hnm : n < m
  · have hlt := onePassEventPosition_lt_of_cut_lt H n m j i hnm
    omega
  omega

/-- Inside one cut block, a position determines the event index. -/
theorem onePassEventPosition_injective_same_cut
    (H : Ordered3Graph Nat) (m : Nat)
    (i j : Fin (onePassBlock H m).length)
    (h : onePassEventPosition H m i =
      onePassEventPosition H m j) : i = j := by
  apply Fin.ext
  dsimp [onePassEventPosition] at h
  omega

/-- Exact selected singleton class test: target positive incidence at
this event is equivalent to the chosen ACTUAL source finite germ.

Notably, the reverse implication must exclude a source edge copy, an
edge from another original cut and a marker/pair-event edge. -/
theorem onePassRawTarget_singleton_incidence_iff
    (H : Ordered3Graph Nat) (m u : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g) :
    (onePassRawTarget H).edge 0
      (onePassEventPosition H m i) (onePassOldImage H u) ↔
      IsLeaf H u ∧ m ≤ u ∧ oneGermCode H m u = g := by
  constructor
  · intro he
    rcases he with hOld | hNew
    · obtain ⟨a,b,c,habc,hx,hy,hz⟩ := hOld
      exact False.elim
        ((onePassEventPosition_ne_oldImage H m i b) hy)
    · obtain ⟨n,j,_,hOne|hTwo⟩ := hNew
      · obtain ⟨g',hget',hMarker|hInc⟩ := hOne
        · obtain ⟨hx,hy,hz⟩ := hMarker
          have hge := onePassEventPosition_ge_three H m i
          omega
        · obtain ⟨u',hu',hnu',hcode',hx,hy,hz⟩ := hInc
          have hnm : n = m :=
            onePassEventPosition_eq_cut H n m j i hy.symm
          subst n
          have hji : j = i :=
            onePassEventPosition_injective_same_cut H m j i hy.symm
          subst j
          have hgg : g' = g := by
            have heq : BlockEvent.singleton m g' =
                BlockEvent.singleton m g := hget'.symm.trans hget
            injection heq
          have huu : u = u' :=
            (onePassOldImage_strictMono H).injective hz
          subst u'
          subst g'
          exact ⟨hu', hnu', hcode'⟩
      · obtain ⟨g',hget',hMarker|hInc⟩ := hTwo
        · obtain ⟨hx,hy,hz⟩ := hMarker
          have hge := onePassEventPosition_ge_three H m i
          omega
        · obtain ⟨a,b,ha,hb,hna,hab,hcode,hx,hy,hz⟩ := hInc
          have hge := onePassEventPosition_ge_three H n j
          omega
  · rintro ⟨hu,hmu,hcode⟩
    exact onePassRawTarget_singleton_incidence H m u i g hget hu hmu hcode

/-- Exact selected full pair-germ test. An incidence at the selected
2-split is positive if and ONLY if the original ordered source pair
has the designated finite full-pair germ. -/
theorem onePassRawTarget_pair_incidence_iff
    (H : Ordered3Graph Nat) (m u v : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g) :
    (onePassRawTarget H).edge
      (onePassEventPosition H m i)
      (onePassOldImage H u) (onePassOldImage H v) ↔
      IsLeaf H u ∧ IsLeaf H v ∧
      m ≤ u ∧ u < v ∧ twoGermCode H m u v = g := by
  constructor
  · intro he
    rcases he with hOld | hNew
    · obtain ⟨a,b,c,habc,hx,hy,hz⟩ := hOld
      exact False.elim
        ((onePassEventPosition_ne_oldImage H m i a) hx)
    · obtain ⟨n,j,_,hOne|hTwo⟩ := hNew
      · obtain ⟨g',hget',hMarker|hInc⟩ := hOne
        · obtain ⟨hx,hy,hz⟩ := hMarker
          have hge := onePassEventPosition_ge_three H m i
          omega
        · obtain ⟨a,ha,hna,hcode,hx,hy,hz⟩ := hInc
          have hge := onePassEventPosition_ge_three H m i
          omega
      · obtain ⟨g',hget',hMarker|hInc⟩ := hTwo
        · obtain ⟨hx,hy,hz⟩ := hMarker
          have hge := onePassEventPosition_ge_three H m i
          omega
        · obtain ⟨u',v',hu',hv',hnu',huv',hcode',hx,hy,hz⟩ := hInc
          have hmn : m = n :=
            onePassEventPosition_eq_cut H m n i j hx
          subst n
          have hij : i = j :=
            onePassEventPosition_injective_same_cut H m i j hx
          subst j
          have hgg : g' = g := by
            have heq : BlockEvent.pair m g' =
                BlockEvent.pair m g := hget'.symm.trans hget
            injection heq
          have huu : u = u' :=
            (onePassOldImage_strictMono H).injective hy
          have hvv : v = v' :=
            (onePassOldImage_strictMono H).injective hz
          subst u'
          subst v'
          subst g'
          exact ⟨hu', hv', hnu', huv', hcode'⟩
  · rintro ⟨hu,hv,hmu,huv,hcode⟩
    exact onePassRawTarget_pair_incidence
      H m u v i g hget hu hv hmu huv hcode

end DiaryLeafPriority
end ThreeUniformDiaries
