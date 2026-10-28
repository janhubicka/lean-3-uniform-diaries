import ThreeUniformDiaries.DiaryFiniteDummyTailProtectedCompletion

/-!
# One countable diary simultaneously completes a family of protected pictures

The existing finite protected completion theorem chooses a tail
extension and then a countable one-pass diary for one finite
protected picture. Its choice of dummy-tail bits actually depends
ONLY on the ambient finite V/E pre-diary, not on the protected set.

Make that uniformity explicit: choose the tail once, then preserve
singleton and full numerical meets of EVERY member of an arbitrary
family of separately protected pictures in the SAME countable
diary. No finiteness of the family index type is required.

This is a genuine simultaneous completion theorem, not a mere
existence assertion separately for each source flip. However the
pictures need only be protected INDIVIDUALLY; the theorem does not
promise that their union is protected or that numerical meets
between vertices from different pictures are source-preserved.
It also does not prove universal finite flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A single dummy-tail choice and single countable one-pass diary
simultaneously preserve all singleton/full numerical meets within
every individually protected picture of a common finite pre-diary.

The induced finite old edge table is preserved once and for all,
independently of the protected picture index. -/
theorem exists_countableDiary_completes_protectedFamily
    {H : Ordered3Graph Nat} {n : Nat} {ι : Type*}
    (P : FiniteRolePrediaryBlock H n)
    (F : ι → Finset Nat)
    (Q : ∀ i : ι, FiniteProtectedMeetPicture H (F i))
    (hBound : ∀ (i : ι) (u : Nat), u ∈ F i → u < n) :
    ∃ bits : Nat → Bool,
      RoleDiary
        (onePassRawTarget (finiteDummyTailCarrier H n bits)) ∧
      (∀ i : ι,
        (∀ u v : Nat,
          u ∈ finiteProtectedWithMarkers (F i) →
          v ∈ finiteProtectedWithMarkers (F i) →
          (onePassRawTarget (finiteDummyTailCarrier H n bits)).oneMeetLevel
            (onePassOldImage (finiteDummyTailCarrier H n bits) u)
            (onePassOldImage (finiteDummyTailCarrier H n bits) v) =
          onePassOldImage (finiteDummyTailCarrier H n bits)
            (H.oneMeetLevel u v)) ∧
        (∀ a b c d : Nat,
          a ∈ finiteProtectedWithMarkers (F i) →
          b ∈ finiteProtectedWithMarkers (F i) →
          c ∈ finiteProtectedWithMarkers (F i) →
          d ∈ finiteProtectedWithMarkers (F i) →
          a < b → c < d →
          (onePassRawTarget (finiteDummyTailCarrier H n bits)).twoMeetLevel
            (onePassOldImage (finiteDummyTailCarrier H n bits) a)
            (onePassOldImage (finiteDummyTailCarrier H n bits) b)
            (onePassOldImage (finiteDummyTailCarrier H n bits) c)
            (onePassOldImage (finiteDummyTailCarrier H n bits) d) =
          onePassOldImage (finiteDummyTailCarrier H n bits)
            (H.twoMeetLevel a b c d))) ∧
      (∀ a b c : Nat, c < n →
        ((onePassRawTarget (finiteDummyTailCarrier H n bits)).edge
            (onePassOldImage (finiteDummyTailCarrier H n bits) a)
            (onePassOldImage (finiteDummyTailCarrier H n bits) b)
            (onePassOldImage (finiteDummyTailCarrier H n bits) c) ↔
          H.edge a b c)) := by
  obtain ⟨bits, PG⟩ := exists_finiteDummyTailCarrier_prediary P
  let G := finiteDummyTailCarrier H n bits
  refine ⟨bits, onePassRawTarget_isDiary PG, ?_, ?_⟩
  · intro i
    have QG : FiniteProtectedMeetPicture G (F i) :=
      finiteDummyTail_preserves_protected_picture
        P (Q i) (hBound i) bits
    refine ⟨?_, ?_⟩
    · intro u v hu hv
      have hTail :=
        onePass_finiteProtectedWithMarkers_oneMeet PG QG u v hu hv
      have hSource :=
        finiteDummyTailCarrier_old_oneMeet_exact
          P.frame bits u v
          (finiteDummyTail_marked_source_bound P (hBound i) u hu)
          (finiteDummyTail_marked_source_bound P (hBound i) v hv)
      exact hTail.trans (congrArg (onePassOldImage G) hSource)
    · intro a b c d ha hb hc hd hab hcd
      have hTail :=
        onePass_finiteProtectedWithMarkers_twoMeet PG QG
          a b c d ha hb hc hd hab hcd
      have hSource :=
        finiteDummyTailCarrier_old_twoMeet_exact P.frame bits
          a b c d
          (finiteDummyTail_marked_source_bound P (hBound i) a ha)
          (finiteDummyTail_marked_source_bound P (hBound i) b hb)
          (finiteDummyTail_marked_source_bound P (hBound i) c hc)
          (finiteDummyTail_marked_source_bound P (hBound i) d hd)
      exact hTail.trans (congrArg (onePassOldImage G) hSource)
  · intro a b c hc
    exact (onePassRawTarget_edge_image_iff G a b c).trans
      (finiteDummyTailCarrier_finite_edge_iff
        P.frame bits a b c hc)

end DiaryLeafPriority
end ThreeUniformDiaries
