import ThreeUniformDiaries.DiaryOnePassFreshSuccessorCuts
import ThreeUniformDiaries.DiaryOnePassIndexCoverage

/-!
# Exactly which type tests can occur at finite-block event levels?

The target's verified E1--E5 classification has an important
consequence missing from the abstract one-hot class argument:
a 1-split event cannot occur in the FIRST coordinate of an
increasing hyperedge; a 2-split event cannot occur in the MIDDLE
coordinate. Thus:

* a complete singleton-type test vector through the events of
  B_m only needs the fresh singleton events and their marker-0
  incidences;
* the auxiliary pair-type tests through B_m only need the fresh
  pair events and their selected full pair-class incidences.

These statements quantify over the ACTUAL target edges at every
indexed event. They do not require that the whole output is a diary
or that source and target cut partitions already agree.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- An actual 1-split cannot appear in the first coordinate of
any edge, because the E1--E5 shapes permit only a 2-split or
a leaf at a nonmarker first coordinate. -/
theorem onePassRawTarget_oneSplit_no_first
    (P : RolePrediary H) (e u v : Nat)
    (he : IsOneSplit (onePassRawTarget H) e) :
    ¬ (onePassRawTarget H).edge e u v := by
  have hNotTwo : ¬ IsTwoSplit (onePassRawTarget H) e := by
    intro ht
    exact he.2.2 ht.2.2
  have hNotLeaf : ¬ IsLeaf (onePassRawTarget H) e := by
    intro hl
    exact hl.2.1 he.2.1
  intro hEdge
  rcases onePassRawTarget_permitted_edge P e u v hEdge with
      hRole | hSplit | hTwo | hDevlin | hNormal
  · have hge := he.1
    omega
  · have hge := he.1
    omega
  · exact hNotTwo hTwo.1
  · have hge := he.1
    rcases hDevlin.1 with h | h <;> omega
  · exact hNotLeaf hNormal.1

/-- Fresh singleton events contribute NO auxiliary pair-type
test at all, including for pairs of original leaves. -/
theorem onePassRawTarget_freshOne_no_aux_test
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g)
    (u v : Nat) :
    ¬ (onePassRawTarget H).edge
      (onePassEventPosition H m i) u v := by
  exact onePassRawTarget_oneSplit_no_first P
    (onePassEventPosition H m i) u v
    (onePassRawTarget_fresh_oneSplit H m i g hget)

/-- Fresh pair events contribute NO singleton middle-column
type tests, even for arbitrary original leaf images. -/
theorem onePassRawTarget_freshTwo_no_one_test
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g)
    (a u : Nat) :
    ¬ (onePassRawTarget H).edge a
       (onePassEventPosition H m i) u := by
  exact onePassRawTarget_twoSplit_no_middle P
    (onePassEventPosition H m i) a u
    (onePassRawTarget_fresh_twoSplit H m i g hget)

/-- The entire singleton type-test vector through block B_m
equals the vector of its actual marker-0 singleton-event bits.
All earlier-coordinate tests at 2-events are uniformly false,
and nonzero earlier-coordinate tests at 1-events are false. -/
theorem onePassBlock_all_one_tests_iff_singleton_event_bits
    (P : RolePrediary H) (m u v : Nat) :
    (∀ (i : Fin (onePassBlock H m).length) (a : Nat),
      a < onePassEventPosition H m i →
        ((onePassRawTarget H).edge a
           (onePassEventPosition H m i) u ↔
         (onePassRawTarget H).edge a
           (onePassEventPosition H m i) v)) ↔
    (∀ (i : Fin (onePassBlock H m).length)
      (g : OneGermSpace m),
      onePassEventAt H m i = BlockEvent.singleton m g →
        ((onePassRawTarget H).edge 0
           (onePassEventPosition H m i) u ↔
         (onePassRawTarget H).edge 0
           (onePassEventPosition H m i) v)) := by
  constructor
  · intro hall i g hget
    have hpos := onePassEventPosition_ge_three H m i
    exact hall i 0 (by omega)
  · intro hSelected i a ha
    rcases onePass_event_label_at_own_cut H m i with
        ⟨g, hPair⟩ | ⟨g, hOne⟩
    · exact iff_of_false
        (onePassRawTarget_freshTwo_no_one_test P m i g hPair a u)
        (onePassRawTarget_freshTwo_no_one_test P m i g hPair a v)
    · by_cases hzero : a = 0
      · subst a
        exact hSelected i g hOne
      · have hrole := onePassRawTarget_fresh_oneSplit H m i g hOne
        exact iff_of_false
          (onePassRawTarget_oneSplit_no_nonzero_middle P
            (onePassEventPosition H m i) a u hrole hzero)
          (onePassRawTarget_oneSplit_no_nonzero_middle P
            (onePassEventPosition H m i) a v hrole hzero)

/-- The entire auxiliary pair type-test vector through B_m
equals the actual full-pair incidence vector at its 2-events.
Every 1-event is uniformly negative in the first coordinate. -/
theorem onePassBlock_all_aux_tests_iff_pair_event_bits
    (P : RolePrediary H) (m a b c d : Nat) :
    (∀ i : Fin (onePassBlock H m).length,
      ((onePassRawTarget H).edge
          (onePassEventPosition H m i) a b ↔
       (onePassRawTarget H).edge
          (onePassEventPosition H m i) c d)) ↔
    (∀ (i : Fin (onePassBlock H m).length)
      (g : TwoGermSpace m),
      onePassEventAt H m i = BlockEvent.pair m g →
        ((onePassRawTarget H).edge
            (onePassEventPosition H m i) a b ↔
         (onePassRawTarget H).edge
            (onePassEventPosition H m i) c d)) := by
  constructor
  · intro hall i g hget
    exact hall i
  · intro hSelected i
    rcases onePass_event_label_at_own_cut H m i with
        ⟨g, hPair⟩ | ⟨g, hOne⟩
    · exact hSelected i g hPair
    · exact iff_of_false
        (onePassRawTarget_freshOne_no_aux_test P m i g hOne a b)
        (onePassRawTarget_freshOne_no_aux_test P m i g hOne c d)

end DiaryLeafPriority
end ThreeUniformDiaries
