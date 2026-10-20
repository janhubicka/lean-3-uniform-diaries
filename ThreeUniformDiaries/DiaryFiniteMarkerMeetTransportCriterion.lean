import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection

/-!
# A precise marker criterion for numerical singleton meet transport

For two nonmarker source vertices, suppose their genuine singleton
meet either lies below the three distinguished marker levels, or
is the capped minimum of those two vertices. Suppose the target
pair enjoys the SAME dichotomy. This situation is supplied by
the E-only split-vertex lemma under genuine diary role hypotheses.

Then preservation and reflection of singleton type comparisons
at the three marker cuts is ALREADY sufficient to preserve the
entire numerical meet under an increasing marker-fixing map.
No arbitrary cut-by-cut type transport is necessary.

This is the exact algebraic bridge needed for the mixed split/leaf
part of the induced source-flip pullback problem. The theorem
states its hypotheses explicitly and does not assert any
every-target-flip absorption or generic role preservation.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A T : Ordered3Graph Nat} {f : Nat → Nat}

/-- For pairs whose first disagreement can only be at a marker
or at their smaller (capping) endpoint, THREE marker prefix tests
determine the complete numeric meet under a marker-fixing map. -/
theorem oneMeet_preserved_of_marker_dichotomy
    (hf : StrictMono f)
    (hMarkers : ∀ x : Nat, x < 3 → f x = x)
    (u v : Nat) (hu3 : 3 ≤ u) (hv3 : 3 ≤ v)
    (hSource :
      A.oneMeetLevel u v < 3 ∨
      A.oneMeetLevel u v = min u v)
    (hTarget :
      T.oneMeetLevel (f u) (f v) < 3 ∨
      T.oneMeetLevel (f u) (f v) = min (f u) (f v))
    (hPrefix : ∀ l : Nat, l ≤ 3 →
      (T.SameOneTypeBelow l (f u) (f v) ↔
        A.SameOneTypeBelow l u v)) :
    T.oneMeetLevel (f u) (f v) = f (A.oneMeetLevel u v) := by
  classical
  have h2 : f 2 = 2 := hMarkers 2 (by omega)
  have hFu3 : 3 ≤ f u := by
    have ht := hf (show 2 < u by omega)
    rw [h2] at ht
    omega
  have hFv3 : 3 ≤ f v := by
    have ht := hf (show 2 < v by omega)
    rw [h2] at ht
    omega
  have hMapMin :
      min (f u) (f v) = f (min u v) := by
    have hm := hf.monotone
    rcases le_total u v with huv | hvu
    · rw [min_eq_left huv, min_eq_left (hm huv)]
    · rw [min_eq_right hvu, min_eq_right (hm hvu)]
  rcases hSource with hSmall | hCap
  · let s := A.oneMeetLevel u v
    have hsSmall : s < 3 := hSmall
    have hsAt : A.SameOneTypeBelow s u v := by
      change A.SameOneTypeBelow (A.oneMeetLevel u v) u v
      exact A.oneMeetLevel_agree u v
    have hsAtT : T.SameOneTypeBelow s (f u) (f v) :=
      (hPrefix s (by omega)).mpr hsAt
    have hsBound : s ≤ min (f u) (f v) := by omega
    have hsLower : s ≤ T.oneMeetLevel (f u) (f v) :=
      Nat.le_findGreatest hsBound hsAtT
    have hsNextFail : ¬ A.SameOneTypeBelow (s + 1) u v := by
      intro hAtNext
      have hCapNext : s + 1 ≤ min u v := by omega
      have hTooLarge : s + 1 ≤ A.oneMeetLevel u v :=
        Nat.le_findGreatest hCapNext hAtNext
      dsimp [s] at *
      omega
    have hsNextFailT :
        ¬ T.SameOneTypeBelow (s + 1) (f u) (f v) := by
      intro ht
      exact hsNextFail ((hPrefix (s + 1) (by omega)).mp ht)
    have hsUpper : T.oneMeetLevel (f u) (f v) < s + 1 := by
      by_contra hbad
      have hGe : s + 1 ≤ T.oneMeetLevel (f u) (f v) := by
        omega
      have hAgree := T.oneMeetLevel_agree (f u) (f v)
      apply hsNextFailT
      intro a b hab hb
      exact hAgree hab (by omega)
    have hFixedS : f s = s := hMarkers s hsSmall
    change T.oneMeetLevel (f u) (f v) = f s
    omega
  · have hSourceAt3 : A.SameOneTypeBelow 3 u v := by
      have hAgree := A.oneMeetLevel_agree u v
      intro a b hab hb
      exact hAgree hab (by rw [hCap]; omega)
    have hTargetAt3 : T.SameOneTypeBelow 3 (f u) (f v) :=
      (hPrefix 3 (by omega)).mpr hSourceAt3
    rcases hTarget with hSmallT | hCapT
    · have hBound3 : 3 ≤ min (f u) (f v) := by omega
      have hTargetGe : 3 ≤ T.oneMeetLevel (f u) (f v) :=
        Nat.le_findGreatest hBound3 hTargetAt3
      omega
    · rw [hCapT,hCap]
      exact hMapMin

end DiaryLeafPriority
end ThreeUniformDiaries
