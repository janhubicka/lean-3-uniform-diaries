import ThreeUniformDiaries.DiaryFiniteMixedAuxiliaryDichotomy

/-!
# Numerical auxiliary meet transport from marker prefixes

The E-only mixed-pair dichotomy says a split-containing
ordered-pair comparison has auxiliary meet either below 3 or
capped at min(first members), with no later strict splitting.

We establish the exact algebraic consequence. Under a strictly
increasing map fixing markers 0,1,2, if BOTH compared graphs
satisfy that dichotomy and the finite marker auxiliary prefixes
at cuts through 3 are reflected exactly, the NUMERICAL auxiliary
meet is preserved.

This is the auxiliary analogue of the singleton marker transport
criterion. It deliberately states all hypotheses instead of
silently assuming inducedness across omitted target vertices.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A T : Ordered3Graph Nat} {f : Nat → Nat}

/-- A small-or-capped auxiliary meet is determined by its prefix
comparisons at markers 0,1,2. Strict monotonicity transports a
capped meet to the corresponding target cap. -/
theorem auxMeet_preserved_of_marker_dichotomy
    (hf : StrictMono f)
    (hMarkers : ∀ x : Nat, x < 3 → f x = x)
    (a b c d : Nat) (ha3 : 3 ≤ a) (hc3 : 3 ≤ c)
    (hSource :
      A.auxMeetLevel a b c d < 3 ∨
        A.auxMeetLevel a b c d = min a c)
    (hTarget :
      T.auxMeetLevel (f a) (f b) (f c) (f d) < 3 ∨
        T.auxMeetLevel (f a) (f b) (f c) (f d) =
          min (f a) (f c))
    (hPrefix : ∀ l : Nat, l ≤ 3 →
      (T.SameAuxTypeBelow l (f a) (f b) (f c) (f d) ↔
        A.SameAuxTypeBelow l a b c d)) :
    T.auxMeetLevel (f a) (f b) (f c) (f d) =
      f (A.auxMeetLevel a b c d) := by
  classical
  have h2 : f 2 = 2 := hMarkers 2 (by omega)
  have hFa3 : 3 ≤ f a := by
    have h := hf (show 2 < a by omega)
    rw [h2] at h
    omega
  have hFc3 : 3 ≤ f c := by
    have h := hf (show 2 < c by omega)
    rw [h2] at h
    omega
  have hMapMin : min (f a) (f c) = f (min a c) := by
    have hm := hf.monotone
    rcases le_total a c with hac | hca
    · rw [min_eq_left hac, min_eq_left (hm hac)]
    · rw [min_eq_right hca, min_eq_right (hm hca)]
  rcases hSource with hSmall | hCap
  · let s := A.auxMeetLevel a b c d
    have hsSmall : s < 3 := hSmall
    have hsAt : A.SameAuxTypeBelow s a b c d := by
      change A.SameAuxTypeBelow (A.auxMeetLevel a b c d) a b c d
      exact A.auxMeetLevel_agree a b c d
    have hsAtT : T.SameAuxTypeBelow s (f a) (f b) (f c) (f d) :=
      (hPrefix s (by omega)).mpr hsAt
    have hsBound : s ≤ min (f a) (f c) := by omega
    have hsLower :
        s ≤ T.auxMeetLevel (f a) (f b) (f c) (f d) :=
      Nat.le_findGreatest hsBound hsAtT
    have hsNextFail : ¬ A.SameAuxTypeBelow (s + 1) a b c d := by
      intro hAtNext
      have hCapNext : s + 1 ≤ min a c := by omega
      have hTooLarge : s + 1 ≤ A.auxMeetLevel a b c d :=
        Nat.le_findGreatest hCapNext hAtNext
      dsimp [s] at *
      omega
    have hsNextFailT :
        ¬ T.SameAuxTypeBelow (s + 1)
            (f a) (f b) (f c) (f d) := by
      intro ht
      exact hsNextFail ((hPrefix (s + 1) (by omega)).mp ht)
    have hsUpper :
        T.auxMeetLevel (f a) (f b) (f c) (f d) < s + 1 := by
      by_contra hbad
      have hGe :
          s + 1 ≤ T.auxMeetLevel (f a) (f b) (f c) (f d) := by
        omega
      have hAgree := T.auxMeetLevel_agree
        (f a) (f b) (f c) (f d)
      apply hsNextFailT
      intro x hx
      exact hAgree (a := x) (by omega)
    have hFixedS : f s = s := hMarkers s hsSmall
    change T.auxMeetLevel (f a) (f b) (f c) (f d) = f s
    omega
  · have hSourceAt3 : A.SameAuxTypeBelow 3 a b c d := by
      have hAgree := A.auxMeetLevel_agree a b c d
      intro x hx
      exact hAgree (a := x) (by rw [hCap]; omega)
    have hTargetAt3 :
        T.SameAuxTypeBelow 3 (f a) (f b) (f c) (f d) :=
      (hPrefix 3 (by omega)).mpr hSourceAt3
    rcases hTarget with hSmallT | hCapT
    · have hBound3 : 3 ≤ min (f a) (f c) := by omega
      have hTargetGe :
          3 ≤ T.auxMeetLevel (f a) (f b) (f c) (f d) :=
        Nat.le_findGreatest hBound3 hTargetAt3
      omega
    · rw [hCapT,hCap]
      exact hMapMin

end DiaryLeafPriority
end ThreeUniformDiaries
