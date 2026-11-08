import ThreeUniformDiaries.DiaryFiniteCandidatePersistentFusion
import ThreeUniformDiaries.DiaryFiniteFrontSafeOrderReserve

/-!
# Track A: persistent finite stages already reserve all future role slots

The familiar relative successor obstruction says a target interval
with no one-/two-split vertex of the required role can block an
arbitrary admissible finite-stage extension.

But the Track A no-escape problem is about a FINITELY PERSISTENT
old stage, not an arbitrary admissible or immediately reserved stage.
For any specified later source split s between two old supported
vertices x<y, the cofinality of canonical full-diary supports
puts s in some future finite stage. Persistence gives a genuine
compatible reserved stage at that later horizon, whose strict order,
role reflection and old image agreement produce an actual target
split of the correct role between f x and f y.

Thus a finitely persistent old stage cannot have the elementary
"missing role slot" obstruction for ANY eventually supported source
split. These are NECESSARY conditions, not a method of producing a
new persistent leaf, and they do not exclude genuine target-image
escape or prove countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A persistent old stage has a target ONE-split at every future
source one-split position lying between two old supported points.
Both endpoints are fixed by the old stage, literally. -/
theorem PersistentReservedDiaryStage.future_oneSplit_slot
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DH : RoleDiary H)
    (P : PersistentReservedDiaryStage H K F m f)
    {x y s : Nat}
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (hxs : x < s) (hsy : s < y)
    (hRole : IsOneSplit H s) :
    ∃ t : Nat, f x < t ∧ t < f y ∧ IsOneSplit K t := by
  classical
  obtain ⟨k, hFull⟩ :=
    countableDiaryFiniteSupport_contains_finset DH (Finset.range (s + 1))
  have hsK : s ∈ countableDiaryFiniteSupport H k :=
    hFull s (Finset.mem_range.mpr (by omega))
  obtain ⟨g, Q, hOld⟩ := P.2 k
  have hmk : m ≤ m + k := by omega
  have hkmk : k ≤ m + k := by omega
  have hxG : x ∈ countableDiaryFiniteSupport H (m + k) :=
    countableDiaryFiniteSupport_mono H m (m + k) hmk hx
  have hyG : y ∈ countableDiaryFiniteSupport H (m + k) :=
    countableDiaryFiniteSupport_mono H m (m + k) hmk hy
  have hsG : s ∈ countableDiaryFiniteSupport H (m + k) :=
    countableDiaryFiniteSupport_mono H k (m + k) hkmk hsK
  have hLeft : g x < g s := Q.1.ordered x s hxG hsG hxs
  have hRight : g s < g y := Q.1.ordered s y hsG hyG hsy
  have hTargetRole : IsOneSplit K (g s) :=
    Q.1.one_split_role s hsG hRole
  rw [hOld x hx] at hLeft
  rw [hOld y hy] at hRight
  exact ⟨g s, hLeft, hRight, hTargetRole⟩

/-- The analogous necessary future TWO-split slot condition.
The old target image gap need not contain every role a priori;
finite persistence forces the correct role for each future split. -/
theorem PersistentReservedDiaryStage.future_twoSplit_slot
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DH : RoleDiary H)
    (P : PersistentReservedDiaryStage H K F m f)
    {x y s : Nat}
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (hxs : x < s) (hsy : s < y)
    (hRole : IsTwoSplit H s) :
    ∃ t : Nat, f x < t ∧ t < f y ∧ IsTwoSplit K t := by
  classical
  obtain ⟨k, hFull⟩ :=
    countableDiaryFiniteSupport_contains_finset DH (Finset.range (s + 1))
  have hsK : s ∈ countableDiaryFiniteSupport H k :=
    hFull s (Finset.mem_range.mpr (by omega))
  obtain ⟨g, Q, hOld⟩ := P.2 k
  have hmk : m ≤ m + k := by omega
  have hkmk : k ≤ m + k := by omega
  have hxG : x ∈ countableDiaryFiniteSupport H (m + k) :=
    countableDiaryFiniteSupport_mono H m (m + k) hmk hx
  have hyG : y ∈ countableDiaryFiniteSupport H (m + k) :=
    countableDiaryFiniteSupport_mono H m (m + k) hmk hy
  have hsG : s ∈ countableDiaryFiniteSupport H (m + k) :=
    countableDiaryFiniteSupport_mono H k (m + k) hkmk hsK
  have hLeft : g x < g s := Q.1.ordered x s hxG hsG hxs
  have hRight : g s < g y := Q.1.ordered s y hsG hyG hsy
  have hTargetRole : IsTwoSplit K (g s) :=
    Q.1.two_split_role s hsG hRole
  rw [hOld x hx] at hLeft
  rw [hOld y hy] at hRight
  exact ⟨g s, hLeft, hRight, hTargetRole⟩

end DiaryLeafPriority
end ThreeUniformDiaries
