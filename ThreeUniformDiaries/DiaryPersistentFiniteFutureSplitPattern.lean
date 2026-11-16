import ThreeUniformDiaries.DiaryPersistentFutureRoleSlots

/-!
# Track A: all finite future one-/two-split role patterns fit in persistent old gaps

The earlier persistent-future-role-slot theorems give a target ONE
or TWO split inside a fixed old image gap for each requested single
future source split. That pointwise existence does NOT assert enough
DISTINCT role slots for two or more different future source positions.

Here genuine finite-horizon persistence is used ONCE for a specified
FINITE set T of future source split positions all between two
already-supported source endpoints x<y. One single later REAL
reserved stage simultaneously maps every s in T to the correct
target role, strictly between the LITERAL fixed old images f(x)
and f(y), and strictly preserves the order of all elements of T.

Consequently all requested split images are pairwise distinct:
persistent stages already satisfy every finite ordered role-slot
occupancy test on each old-supported gap. The output horizon
witness g MAY DEPEND on T. This is a necessary condition for
persistence, not a proof that any arbitrary old stage is persistent,
nor an extension of a new leaf through all source horizons.

English-first adversarial proof:
3-uniform-diaries/notes/
  track_a_persistent_finite_future_split_role_pattern_20261116.md
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Fix a finitely persistent ACTUAL reserved old stage P at source
horizon m and two already-supported source vertices x,y. Any finite
family T of future source genuine 1-/2-splits strictly between x,y
has ONE simultaneous, order-preserving, injective placement inside
the target gap (f(x),f(y)), preserving the role of EACH split.

The witness is obtained from ONE real reserved future horizon
m+k that contains all source split positions in T; it is NOT a
choice of unrelated target positions for each source split.

No guarantee is asserted for a new source leaf, or an arbitrary
admissible/reserved old stage lacking genuine finite persistence. -/
theorem PersistentReservedDiaryStage.future_finite_split_pattern_slots
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DH : RoleDiary H)
    (P : PersistentReservedDiaryStage H K F m f)
    {x y : Nat}
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (T : Finset Nat)
    (hBetween : ∀ s : Nat, s ∈ T → x < s ∧ s < y)
    (hSplit : ∀ s : Nat, s ∈ T →
      IsOneSplit H s ∨ IsTwoSplit H s) :
    ∃ g : Nat → Nat,
      g x = f x ∧ g y = f y ∧
      (∀ s : Nat, s ∈ T →
        f x < g s ∧ g s < f y ∧
        ((IsOneSplit H s ∧ IsOneSplit K (g s)) ∨
         (IsTwoSplit H s ∧ IsTwoSplit K (g s)))) ∧
      (∀ s t : Nat, s ∈ T → t ∈ T → s < t → g s < g t) ∧
      (∀ s t : Nat, s ∈ T → t ∈ T → g s = g t → s = t) := by
  classical
  obtain ⟨k, hFull⟩ :=
    countableDiaryFiniteSupport_contains_finset DH T
  obtain ⟨g, Q, hOld⟩ := P.2 k
  have hmk : m ≤ m + k := by omega
  have hkmk : k ≤ m + k := by omega
  have hxG : x ∈ countableDiaryFiniteSupport H (m + k) :=
    (countableDiaryFiniteSupport_mono H m (m + k) hmk) hx
  have hyG : y ∈ countableDiaryFiniteSupport H (m + k) :=
    (countableDiaryFiniteSupport_mono H m (m + k) hmk) hy
  have hAt (s : Nat) (hs : s ∈ T) :
      s ∈ countableDiaryFiniteSupport H (m + k) :=
    (countableDiaryFiniteSupport_mono H k (m + k) hkmk)
      (hFull s hs)
  have hStrict : ∀ s t : Nat,
      s ∈ T → t ∈ T → s < t → g s < g t := by
    intro s t hs ht hst
    exact Q.1.ordered s t (hAt s hs) (hAt t ht) hst
  refine ⟨g, hOld x hx, hOld y hy, ?_, hStrict, ?_⟩
  · intro s hs
    obtain ⟨hxs, hsy⟩ := hBetween s hs
    have hLeft : g x < g s :=
      Q.1.ordered x s hxG (hAt s hs) hxs
    have hRight : g s < g y :=
      Q.1.ordered s y (hAt s hs) hyG hsy
    rw [hOld x hx] at hLeft
    rw [hOld y hy] at hRight
    rcases hSplit s hs with hOne | hTwo
    · exact ⟨hLeft, hRight, Or.inl
        ⟨hOne, Q.1.one_split_role s (hAt s hs) hOne⟩⟩
    · exact ⟨hLeft, hRight, Or.inr
        ⟨hTwo, Q.1.two_split_role s (hAt s hs) hTwo⟩⟩
  · intro s t hs ht hEq
    rcases lt_trichotomy s t with hst | heq | hts
    · have hLt := hStrict s t hs ht hst
      omega
    · exact heq
    · have hLt := hStrict t s ht hs hts
      omega

end DiaryLeafPriority
end ThreeUniformDiaries
