import ThreeUniformDiaries.DiaryUpperBoundNonmarkerAuxMeet
import ThreeUniformDiaries.DiaryFiniteInducedMarkerPrefix

/-!
# Track A: finite induced diary preembedding is genuinely auxiliary-type-respecting

The finite diary upper-bound factorisation requires the FULL
FiniteAuxEmbedding interface, not merely selected leaf meet preservation.

The earlier induced finite leaf-preembedding lemma already preserves:
* numerical meets of every nonmarker singleton pair;
* auxiliary meets of every two ordered nonmarker pairs
  (including leaf/leaf and mixed split/leaf pairs).

This module discharges the remaining cases where one of the
singleton coordinates, or one of the ordered pair first coordinates,
lies among the three markers 0,1,2. At those cuts every auxiliary
test is itself a literal induced marker triple; no skipped target
coordinate can occur below the cut.

The result is a complete finite auxiliary-type-respecting code,
with no global conditions on the zero-extended tail. It is
independent of the diary Ramsey theorem, flip absorption,
or countable unavoidability.

To apply it to a compressed finite diary support, one must still
construct the induced finite leaf-preembedding and prove its exact
leaf-only S1/S2 meet transport. These are separate tasks.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

variable {A T : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}

/-- At a selected cut below marker 3, inducedness and fixed
0,1,2 alone reflect singleton types for ANY two bounded
source vertices, including markers. -/
theorem finite_marker_oneType_iff_of_induced_all_vertices
    (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 2)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c))
    (w u v : Nat) (hw3 : w < 3)
    (hwu : w ≤ u) (hwv : w ≤ v)
    (hun : u < n) (hvn : v < n) :
    A.SameOneTypeBelow w u v ↔
      T.SameOneTypeBelow (f w) (f u) (f v) := by
  have hfw : f w = w :=
    fixed_three_markers h0 h1 h2 w hw3
  rw [hfw]
  constructor
  · intro hs x y hxy hyw
    have hx3 : x < 3 := by omega
    have hy3 : y < 3 := by omega
    have hfx : f x = x :=
      fixed_three_markers h0 h1 h2 x hx3
    have hfy : f y = y :=
      fixed_three_markers h0 h1 h2 y hy3
    have hEU := hInduced x y u hxy (by omega) hun
    have hEV := hInduced x y v hxy (by omega) hvn
    rw [hfx, hfy] at hEU hEV
    exact hEU.trans ((hs hxy hyw).trans hEV.symm)
  · intro ht x y hxy hyw
    have hx3 : x < 3 := by omega
    have hy3 : y < 3 := by omega
    have hfx : f x = x :=
      fixed_three_markers h0 h1 h2 x hx3
    have hfy : f y = y :=
      fixed_three_markers h0 h1 h2 y hy3
    have hEU := hInduced x y u hxy (by omega) hun
    have hEV := hInduced x y v hxy (by omega) hvn
    rw [hfx, hfy] at hEU hEV
    exact hEU.symm.trans ((ht hxy hyw).trans hEV)

/-- The same complete bounded marker-cut equivalence for auxiliary
2-types of two ordered pairs. A first coordinate may itself be
0,1,2; the only relevant tests are still actual marker triples. -/
theorem finite_marker_auxType_iff_of_induced_all_vertices
    (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 2)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c))
    (w a b c d : Nat) (hw3 : w < 3)
    (hwa : w ≤ a) (hab : a < b)
    (hwc : w ≤ c) (hcd : c < d)
    (hbn : b < n) (hdn : d < n) :
    A.SameAuxTypeBelow w a b c d ↔
      T.SameAuxTypeBelow (f w) (f a) (f b) (f c) (f d) := by
  have hfw : f w = w :=
    fixed_three_markers h0 h1 h2 w hw3
  rw [hfw]
  constructor
  · intro hs x hx
    have hx3 : x < 3 := by omega
    have hfx : f x = x :=
      fixed_three_markers h0 h1 h2 x hx3
    have hAB := hInduced x a b (by omega) hab hbn
    have hCD := hInduced x c d (by omega) hcd hdn
    rw [hfx] at hAB hCD
    exact hAB.trans ((hs hx).trans hCD.symm)
  · intro ht x hx
    have hx3 : x < 3 := by omega
    have hfx : f x = x :=
      fixed_three_markers h0 h1 h2 x hx3
    have hAB := hInduced x a b (by omega) hab hbn
    have hCD := hInduced x c d (by omega) hcd hdn
    rw [hfx] at hAB hCD
    exact hAB.symm.trans ((ht hx).trans hCD)

/-- THE complete finite-ATR transfer: every induced finite leaf
preembedding from a genuine full finite diary into an arbitrary
countable full RoleDiary is auxiliary-type-respecting on ALL
actual source vertices, including the 0,1,2 marker cases.

The proof is by numerical meets for nonmarker coordinates and
literal finite edge tests at the small marker cuts. No fictitious
infinite-source tail is ever assumed aux-type-respecting. -/
theorem FiniteLeafPreembedding.toFiniteAuxEmbedding_of_induced
    (DA : FiniteRoleDiaryBlock A n)
    (DT : RoleDiary T)
    (P : FiniteLeafPreembedding A T n k f)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c)) :
    ThreeUniformDiaries.Ordered3Graph.FiniteAuxEmbedding A T f n := by
  refine {
    strictMono := P.strictMono
    edge_iff := hInduced
    one := ?_
    aux := ?_
  }
  · intro w u v hwu hwv hun hvn
    by_cases hNon : 3 ≤ u ∧ 3 ≤ v
    · have hMeets :
          T.oneMeetLevel (f u) (f v) =
            f (A.oneMeetLevel u v) :=
        finite_induced_all_oneMeet_in_countable
          DA.prediary DT P hInduced
          u v hNon.1 hun hNon.2 hvn
      have hs :=
        A.oneMeetLevel_ge_iff_sameOneTypeBelow
          w u v hwu hwv
      have ht :=
        T.oneMeetLevel_ge_iff_sameOneTypeBelow
          (f w) (f u) (f v)
          (P.strictMono.monotone hwu)
          (P.strictMono.monotone hwv)
      constructor
      · intro hSource
        apply ht.mp
        rw [hMeets]
        exact P.strictMono.monotone (hs.mpr hSource)
      · intro hTarget
        apply hs.mp
        have hle : f w ≤ f (A.oneMeetLevel u v) := by
          simpa only [hMeets] using (ht.mpr hTarget)
        by_contra hn
        have hw : A.oneMeetLevel u v < w :=
          Nat.lt_of_not_ge hn
        exact (not_lt_of_ge hle) (P.strictMono hw)
    · have hw3 : w < 3 := by
        by_contra hn
        have hwge : 3 ≤ w := by omega
        exact hNon ⟨hwge.trans hwu, hwge.trans hwv⟩
      exact finite_marker_oneType_iff_of_induced_all_vertices
        (A := A) (T := T) (f := f) (n := n)
        P.marker_zero P.marker_one P.marker_two hInduced
        w u v hw3 hwu hwv hun hvn
  · intro w a b c d hwa hab hwc hcd hbn hdn
    by_cases hNon : 3 ≤ a ∧ 3 ≤ c
    · have hMeets :
          T.auxMeetLevel (f a) (f b) (f c) (f d) =
            f (A.auxMeetLevel a b c d) :=
        P.auxMeet_nonmarker_of_induced DA DT hInduced
          a b c d hab hcd hNon.1 (by omega) hbn
          hNon.2 (by omega) hdn
      have hs :=
        A.auxMeetLevel_ge_iff_sameAuxTypeBelow
          w a b c d hwa hwc
      have ht :=
        T.auxMeetLevel_ge_iff_sameAuxTypeBelow
          (f w) (f a) (f b) (f c) (f d)
          (P.strictMono.monotone hwa)
          (P.strictMono.monotone hwc)
      constructor
      · intro hSource
        apply ht.mp
        rw [hMeets]
        exact P.strictMono.monotone (hs.mpr hSource)
      · intro hTarget
        apply hs.mp
        have hle : f w ≤ f (A.auxMeetLevel a b c d) := by
          simpa only [hMeets] using (ht.mpr hTarget)
        by_contra hn
        have hw : A.auxMeetLevel a b c d < w :=
          Nat.lt_of_not_ge hn
        exact (not_lt_of_ge hle) (P.strictMono hw)
    · have hw3 : w < 3 := by
        by_contra hn
        have hwge : 3 ≤ w := by omega
        exact hNon ⟨hwge.trans hwa, hwge.trans hwc⟩
      exact finite_marker_auxType_iff_of_induced_all_vertices
        (A := A) (T := T) (f := f) (n := n)
        P.marker_zero P.marker_one P.marker_two hInduced
        w a b c d hw3 hwa hab hwc hcd hbn hdn

end DiaryLeafPriority
end ThreeUniformDiaries
