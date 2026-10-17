import ThreeUniformDiaries.DiaryOnePassFreshTwoCoherence
import ThreeUniformDiaries.DiaryOnePassFullBlockNodup

/-!
# All earlier events in a selected pair event's block are pair events

The one-pass event scheduler places the selected pair-germ events
before ALL singleton-germ events at every original cut. For a selected
pair event at index i, every earlier event index j<i therefore has
the same pair arity.

This index-sensitive fact is needed for the fresh V2 witness proof:
there can be no earlier singleton test on either coordinate of
an ordered leaf pair. The selected/default pair children agree
at the start of B_m and at all earlier pair events (both negative);
their first different pair bit is exactly the designated event i.

The proof concerns actual source-dependent event lists and Fin
indices, not a synthetic event enumeration.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A list containing only singleton constructors can never have
a pair constructor at any optional index. -/
private theorem singleton_event_list_no_pair
    (m : Nat) (ss : List (OneGermSpace m))
    (i : Nat) (g : TwoGermSpace m) :
    (ss.map (BlockEvent.singleton m))[i]? ≠
      some (BlockEvent.pair m g) := by
  induction ss generalizing i with
  | nil =>
    simp
  | cons h tail ih =>
    cases i with
    | zero =>
      simp
    | succ i =>
      simpa only [List.map_cons, List.getElem?_cons_succ]
        using ih i

/-- If a pair event appears at index i in a pair-before-singleton
list, every earlier index j<i also contains a pair event. -/
private theorem pair_before_singleton_in_appended_list
    (m : Nat)
    (ps : List (TwoGermSpace m))
    (ss : List (OneGermSpace m))
    (i j : Nat) (g : TwoGermSpace m)
    (hi : ((ps.map (BlockEvent.pair m)) ++
            (ss.map (BlockEvent.singleton m)))[i]? =
          some (BlockEvent.pair m g))
    (hji : j < i) :
    ∃ k : TwoGermSpace m,
      ((ps.map (BlockEvent.pair m)) ++
       (ss.map (BlockEvent.singleton m)))[j]? =
        some (BlockEvent.pair m k) := by
  induction ps generalizing i j with
  | nil =>
    have hbad := singleton_event_list_no_pair m ss i g
    exact False.elim (hbad (by simpa using hi))
  | cons p tail ih =>
    cases i with
    | zero =>
      omega
    | succ i =>
      cases j with
      | zero =>
        exact ⟨p, by simp⟩
      | succ j =>
        have htail :
            ((tail.map (BlockEvent.pair m)) ++
              (ss.map (BlockEvent.singleton m)))[i]? =
              some (BlockEvent.pair m g) := by
          simpa only [List.map_cons, List.cons_append,
            List.getElem?_cons_succ] using hi
        obtain ⟨k, hj⟩ :=
          ih i j htail (by omega)
        exact ⟨k, by
          simpa only [List.map_cons, List.cons_append,
            List.getElem?_cons_succ] using hj⟩

/-- In the ACTUAL one-pass list of block B_m, if event i is a
pair event then each earlier event j also has pair arity.
In particular no singleton event can precede a pair event. -/
theorem onePass_pair_event_before_singletons
    (H : Ordered3Graph Nat) (m : Nat)
    (i j : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g)
    (hji : j.val < i.val) :
    ∃ k : TwoGermSpace m,
      onePassEventAt H m j = BlockEvent.pair m k := by
  classical
  have hm3 : ¬ m < 3 := by
    have h := onePassEvent_cut_ge_three H m i
    omega
  have hNotTwo : ¬ IsTwoSplit H m :=
    onePass_pair_event_source_not_twoSplit H m i g hget
  let ps := (selectedTwoGerms H m).toList
  let ss := if IsLeaf H m then
    sortOneGermsDescending m (selectedOneGerms H m).toList
    else []
  have hrepr : onePassBlock H m =
      (ps.map (BlockEvent.pair m)) ++
      (ss.map (BlockEvent.singleton m)) := by
    by_cases hleaf : IsLeaf H m
    · simp [onePassBlock, hm3, hNotTwo, hleaf, ps, ss]
    · simp [onePassBlock, hm3, hNotTwo, hleaf, ps, ss]
  have hOptI : ((ps.map (BlockEvent.pair m)) ++
      (ss.map (BlockEvent.singleton m)))[i.val]? =
        some (BlockEvent.pair m g) := by
    rw [← hrepr]
    apply (List.getElem?_eq_some_iff).mpr
    exact ⟨i.isLt, by simpa [onePassEventAt] using hget⟩
  obtain ⟨k, hOptJ⟩ :=
    pair_before_singleton_in_appended_list
      m ps ss i.val j.val g hOptI hji
  refine ⟨k, ?_⟩
  rw [← hrepr] at hOptJ
  obtain ⟨hbound, heq⟩ :=
    (List.getElem?_eq_some_iff).mp hOptJ
  simpa [onePassEventAt] using heq

end DiaryLeafPriority
end ThreeUniformDiaries
