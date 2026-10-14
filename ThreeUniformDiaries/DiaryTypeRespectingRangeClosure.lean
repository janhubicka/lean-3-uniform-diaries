import ThreeUniformDiaries.DiarySelectedCarrierClosure
import ThreeUniformDiaries.DiaryEnvelopeMinimality
import ThreeUniformDiaries.DiaryEmbeddingExactOneMeets

/-!
# Exact full two-type meets and meet-closed type-respecting images

An ordinary type-respecting embedding preserves both endpoint one-type
agreements and full pair-type agreements at corresponding source cuts.
That does not by itself rule out an earlier disagreement at a skipped
target vertex. The upper bound is instead witnessed at the actual
source first-disagreement level, which survives under inducedness.

This proves exact full two-type meet preservation across arbitrary
target gaps. As a consequence, the range of every such embedding is
closed under singleton and full pair meets. This is the missing
abstract minimal-envelope comparison ingredient: all competing
type-respecting images are meet-closed.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Failure of a full pair-type agreement immediately after a source
level survives at the selected target level of any induced increasing
embedding. The first witness can be in either singleton coordinate
or in the auxiliary pair bit. -/
theorem twoType_failure_at_image_cut
    (H K : Ordered3Graph Nat)
    (ψ : Embedding H K)
    (w a b c d : Nat)
    (hwa : w < a) (hab : a < b)
    (hwc : w < c) (hcd : c < d)
    (hsource : H.SameTwoTypeBelow w a b c d)
    (hfail : ¬ H.SameTwoTypeBelow (w+1) a b c d) :
    ¬ K.SameTwoTypeBelow (ψ w+1)
      (ψ a) (ψ b) (ψ c) (ψ d) := by
  classical
  intro htarget
  have hedge : ∀ x y z : Nat, x < y → y < z →
      (H.edge x y z ↔ K.edge (ψ x) (ψ y) (ψ z)) := by
    intro x y z hxy hyz
    exact ψ.edge_iff hxy hyz
  have hwb : w < b := lt_trans hwa hab
  have hwd : w < d := lt_trans hwc hcd
  have hnextA : H.SameOneTypeBelow (w+1) a c := by
    by_contra hn
    exact (H.oneType_failure_at_image_cut K ψ.toFun ψ.strictMono hedge
      w a c hwa hwc hsource.1 hn) htarget.1
  have hnextB : H.SameOneTypeBelow (w+1) b d := by
    by_contra hn
    exact (H.oneType_failure_at_image_cut K ψ.toFun ψ.strictMono hedge
      w b d hwb hwd hsource.2.1 hn) htarget.2.1
  have hnextAux : H.SameAuxTypeBelow (w+1) a b c d := by
    by_contra hn
    exact (H.auxType_failure_at_image_cut K ψ.toFun ψ.strictMono hedge
      w a b c d hwa hab hwc hcd hn hsource.2.2) htarget.2.2
  exact hfail ⟨hnextA, hnextB, hnextAux⟩

/-- Every ordinary type-respecting embedding preserves exact capped
full 2-type meet levels. No convexity of its target image is assumed. -/
theorem typeRespecting_twoMeetLevel_eq
    {H K : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (a b c d : Nat) (hab : a < b) (hcd : c < d) :
    K.twoMeetLevel (ψ a) (ψ b) (ψ c) (ψ d) =
      ψ (H.twoMeetLevel a b c d) := by
  classical
  let w := H.twoMeetLevel a b c d
  have hbound : w ≤ min a c := H.twoMeetLevel_le_min a b c d
  have hwa : w ≤ a := hbound.trans (min_le_left _ _)
  have hwc : w ≤ c := hbound.trans (min_le_right _ _)
  have hsource : H.SameTwoTypeBelow w a b c d :=
    H.twoMeetLevel_agree a b c d
  have htarget : K.SameTwoTypeBelow (ψ w)
      (ψ a) (ψ b) (ψ c) (ψ d) :=
    (hψ.two w a b c d hwa hab hwc hcd).mp hsource
  have hlow : ψ w ≤
      K.twoMeetLevel (ψ a) (ψ b) (ψ c) (ψ d) := by
    exact Nat.le_findGreatest
      (le_min (ψ.strictMono.monotone hwa)
        (ψ.strictMono.monotone hwc)) htarget
  by_cases hcap : w = min a c
  · have hmin : min (ψ a) (ψ c) = ψ (min a c) := by
      rcases le_total a c with hac | hca
      · simp [min_eq_left hac,
          min_eq_left (ψ.strictMono.monotone hac)]
      · simp [min_eq_right hca,
          min_eq_right (ψ.strictMono.monotone hca)]
    have hupper : K.twoMeetLevel (ψ a) (ψ b) (ψ c) (ψ d) ≤ ψ w := by
      rw [hcap, ← hmin]
      exact K.twoMeetLevel_le_min (ψ a) (ψ b) (ψ c) (ψ d)
    exact Nat.le_antisymm hupper hlow
  · have hstrict : w < min a c := by omega
    have hwa' : w < a := lt_of_lt_of_le hstrict (min_le_left _ _)
    have hwc' : w < c := lt_of_lt_of_le hstrict (min_le_right _ _)
    have hfail : ¬ H.SameTwoTypeBelow (w+1) a b c d := by
      intro hnext
      have hn : w + 1 ≤ min a c := by omega
      have hh : w + 1 ≤ H.twoMeetLevel a b c d :=
        Nat.le_findGreatest hn hnext
      omega
    have hfailK := H.twoType_failure_at_image_cut K ψ
      w a b c d hwa' hab hwc' hcd hsource hfail
    have hupper : K.twoMeetLevel (ψ a) (ψ b) (ψ c) (ψ d) ≤ ψ w := by
      by_contra hn
      have hnext : ψ w + 1 ≤
          K.twoMeetLevel (ψ a) (ψ b) (ψ c) (ψ d) := by omega
      have hagree := K.twoMeetLevel_agree (ψ a) (ψ b) (ψ c) (ψ d)
      have htargetNext : K.SameTwoTypeBelow (ψ w+1)
          (ψ a) (ψ b) (ψ c) (ψ d) := by
        refine ⟨?_, ?_, ?_⟩
        · intro x y hxy hy
          exact hagree.1 hxy (lt_of_lt_of_le hy hnext)
        · intro x y hxy hy
          exact hagree.2.1 hxy (lt_of_lt_of_le hy hnext)
        · intro x hx
          exact hagree.2.2 (lt_of_lt_of_le hx hnext)
      exact hfailK htargetNext
    exact Nat.le_antisymm hupper hlow

namespace Embedding

/-- Every type-respecting image is closed under the manuscript's
singleton and complete ordered-pair meets, with any number of
skipped target vertices. -/
theorem TypeRespecting.range_meet_closed
    {H K : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting) :
    K.IsMeetClosed (Set.range ψ.toFun) := by
  constructor
  · intro u v hu hv
    rcases hu with ⟨a, rfl⟩
    rcases hv with ⟨b, rfl⟩
    refine ⟨H.oneMeetLevel a b, ?_⟩
    exact (typeRespecting_oneMeetLevel_eq ψ hψ a b).symm
  · intro u v x y hu hv hx hy huv hxy
    rcases hu with ⟨a, rfl⟩
    rcases hv with ⟨b, rfl⟩
    rcases hx with ⟨c, rfl⟩
    rcases hy with ⟨d, rfl⟩
    have hab : a < b := by
      by_contra hn
      have hle : b ≤ a := Nat.le_of_not_gt hn
      have hmap : ψ b ≤ ψ a := ψ.strictMono.monotone hle
      omega
    have hcd : c < d := by
      by_contra hn
      have hle : d ≤ c := Nat.le_of_not_gt hn
      have hmap : ψ d ≤ ψ c := ψ.strictMono.monotone hle
      omega
    refine ⟨H.twoMeetLevel a b c d, ?_⟩
    exact (typeRespecting_twoMeetLevel_eq ψ hψ a b c d hab hcd).symm

end Embedding

/-- A least meet-closed carrier is contained in every competing
type-respecting image containing the same protected prefix and
distinguished endpoints. This turns the selected carrier's verified
least-closure property into a minimality statement for actual
type-respecting images. -/
theorem minimalMeetEnvelope_subset_typeRespecting_range
    (K : Ordered3Graph Nat) (j a b : Nat) (S : Set Nat)
    (hminimal : K.IsMinimalMeetEnvelope j a b S)
    {H : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (hprefix : ∀ t, t < j → t ∈ Set.range ψ.toFun)
    (ha : a ∈ Set.range ψ.toFun) (hb : b ∈ Set.range ψ.toFun) :
    S ⊆ Set.range ψ.toFun :=
  hminimal.2.2.2.2 (Set.range ψ.toFun)
    (Embedding.TypeRespecting.range_meet_closed ψ hψ) hprefix ha hb

end Ordered3Graph
end ThreeUniformDiaries
