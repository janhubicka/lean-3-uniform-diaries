import ThreeUniformDiaries.DiaryFiniteSupportRelationalFactor

/-!
# Every protected singleton meet survives finite support extraction

The finite support contains the *entire* image of the given finite
diary copy, not merely its leaf vertices. Hence whenever the source
singleton meet is not capped, the source first disagreement is at
a genuine source vertex m, witnessed by another source vertex x<m.
Both vertices remain in the support. The induced relational
factorisation retains precisely that disagreement in the finite
compression, giving the missing upper bound for the meet.

For a capped meet the strict increasing rank map preserves the
minimum. In both cases the lower bound comes from the already
verified forward-only type transport from the ambient G.
This works for all source nonmarker pairs, including split/leaf
mixed comparisons, and never asserts an invalid general converse
to type transport on arbitrary finite supports.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A G : Ordered3Graph Nat} {S : Finset Nat}
variable {n : Nat} {f : Nat → Nat}

/-- Exact numerical singleton-meet preservation for every pair
of source nonmarker vertices in a supplied finite meet embedding,
after compressing the ambient target onto ANY finite support
containing the whole finite image. -/
theorem finiteSupportLift_oneMeet_exact
    (E : FiniteMeetEmbedding A G n f)
    (hRange : ∀ u, u < n → f u ∈ S)
    (u v : Nat) (hu3 : 3 ≤ u) (hu : u < n)
    (hv3 : 3 ≤ v) (hv : v < n) :
    (finiteSupportGraph G S).oneMeetLevel
      (finiteSupportLift S n f u) (finiteSupportLift S n f v) =
        finiteSupportLift S n f (A.oneMeetLevel u v) := by
  classical
  let H := finiteSupportGraph G S
  let g := finiteSupportLift S n f
  let m := A.oneMeetLevel u v
  have hmBound : m ≤ min u v := A.oneMeetLevel_le_min u v
  have hm : m < n := by omega
  have hmU : m ≤ u := hmBound.trans (min_le_left _ _)
  have hmV : m ≤ v := hmBound.trans (min_le_right _ _)
  have hg : StrictMono g :=
    finiteSupportLift_strictMono S n f E.strictMono hRange
  have hgmU : g m ≤ g u := hg.monotone hmU
  have hgmV : g m ≤ g v := hg.monotone hmV
  have sm := finiteSupportLift_spec S n f hRange m hm
  have su := finiteSupportLift_spec S n f hRange u hu
  have sv := finiteSupportLift_spec S n f hRange v hv
  have hOldMeet : G.oneMeetLevel (f u) (f v) = f m := by
    dsimp [m]
    exact E.oneMeet u v hu3 hu hv3 hv
  have hOldAt : G.SameOneTypeBelow (f m) (f u) (f v) := by
    rw [← hOldMeet]
    exact G.oneMeetLevel_agree (f u) (f v)
  have hNewAt : H.SameOneTypeBelow (g m) (g u) (g v) :=
    finiteSupportGraph_oneType_of_original
      (G := G) (S := S) (g m) (g u) (g v)
      sm.1 su.1 sv.1 hgmU hgmV
      (by
        change G.SameOneTypeBelow
          (finiteSupportIndex S (finiteSupportLift S n f m))
          (finiteSupportIndex S (finiteSupportLift S n f u))
          (finiteSupportIndex S (finiteSupportLift S n f v))
        rw [sm.2,su.2,sv.2]
        exact hOldAt)
  have hLower : g m ≤ H.oneMeetLevel (g u) (g v) :=
    Nat.le_findGreatest (le_min hgmU hgmV) hNewAt
  have hUpper : H.oneMeetLevel (g u) (g v) ≤ g m := by
    by_cases hCap : m = min u v
    · have hMin : g m = min (g u) (g v) := by
        rcases le_total u v with huv | hvu
        · have hmu : m = u := by
            simpa only [min_eq_left huv] using hCap
          rw [hmu,min_eq_left (hg.monotone huv)]
        · have hmv : m = v := by
            simpa only [min_eq_right hvu] using hCap
          rw [hmv,min_eq_right (hg.monotone hvu)]
      have hBound := H.oneMeetLevel_le_min (g u) (g v)
      omega
    · have hStrict : m < min u v := by omega
      have hmu : m < u := by omega
      have hmv : m < v := by omega
      have hAAt : A.SameOneTypeBelow m u v :=
        A.oneMeetLevel_agree u v
      have hFail : ¬ A.SameOneTypeBelow (m + 1) u v := by
        intro hNext
        have hTooLarge : m + 1 ≤ A.oneMeetLevel u v :=
          Nat.le_findGreatest (by omega) hNext
        dsimp [m] at hTooLarge
        omega
      have hNotAll : ¬ ∀ x : Nat, x < m →
          (A.edge x m u ↔ A.edge x m v) := by
        intro hAll
        exact hFail
          ((A.sameOneTypeBelow_succ_iff m u v).mpr
            ⟨hAAt,hAll⟩)
      obtain ⟨x,hNotAtX⟩ := not_forall.mp hNotAll
      obtain ⟨hxm,hDifferent⟩ := not_imp.mp hNotAtX
      have hXu : H.edge (g x) (g m) (g u) ↔
          A.edge x m u :=
        finiteSupportLift_edge_iff
          E hRange x m u hxm hmu hu
      have hXv : H.edge (g x) (g m) (g v) ↔
          A.edge x m v :=
        finiteSupportLift_edge_iff
          E hRange x m v hxm hmv hv
      have hTargetDiff : ¬
          (H.edge (g x) (g m) (g u) ↔
           H.edge (g x) (g m) (g v)) := by
        intro hSame
        exact hDifferent (hXu.symm.trans (hSame.trans hXv))
      by_contra hTooLarge
      have hAbove : g m < H.oneMeetLevel (g u) (g v) := by omega
      exact hTargetDiff
        ((H.oneMeetLevel_agree (g u) (g v))
          (hg hxm) hAbove)
  change H.oneMeetLevel (g u) (g v) = g m
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
