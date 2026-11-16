import ThreeUniformDiaries.DiaryPersistentInternalGapStableProfile

/-!
# Track A: the SAME horizon-stable bounded internal profile is numerically exact on its generators

The verified bounded internal-gap compactness theorem supplies ONE
finite joint image profile p of any finite set T strictly between
two OLD supported source positions x,y. The SAME p occurs in genuine
reserved stages fixing the original old f throughout ALL later
finite source horizons, with the same strict order, actual roles,
and induced E5 triples/nontriples on T.

We strengthen this on exactly those SOURCE S1 singleton-meet and
S2 ordered-pair-meet generators which themselves belong to T:
the corresponding NUMERIC target oneMeet / twoMeet equals p of
the actual source generator.

We do NOT infer exact numerical S1/S2 from induced hypergraph
edges alone. Instead choose one genuine later reserved stage
which BOTH realizes p and whose supported source region contains
the WHOLE finite T, using the independent full-diary cofinal
support theorem. Its actual leaf_oneMeet/leaf_twoMeet obligations
give all exact generator equations simultaneously.

This still says nothing about the new rightmost selected source
leaf m, whose image is NOT bounded between two previously fixed
old source vertices. No countable diary unavoidability follows.

English-first proof:
notes/track_a_internal_gap_stable_exact_S1_S2_meets_20261116.md
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The joint FINITE internal-gap image table selected from a
genuinely persistent old stage simultaneously has:
  * a genuine full-old-compatible reserved realization at EVERY
    future horizon m+k+n;
  * exact numerical target S1 singleton meets on leaf pairs whose
    source meet generator is INCLUDED in T;
  * exact numerical target S2 ordered-pair meets on leaf quadruples
    whose source full pair generator is INCLUDED in T.

A single table p and a single horizon offset k serve ALL clauses.
An actual later supported stage validates the S1/S2 equations,
not a bare candidate or an incorrect inducedness-to-meet shortcut.

The selected image of a source leaf OUTSIDE the old fixed gap
may still escape. This is not a full persistent next stage. -/
theorem PersistentReservedDiaryStage.exists_internal_gap_stable_exact_leaf_meet_profile
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DH : RoleDiary H)
    (P : PersistentReservedDiaryStage H K F m f)
    {x y : Nat}
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (T : Finset Nat)
    (hBetween : ∀ s : Nat, s ∈ T → x < s ∧ s < y) :
    ∃ k : Nat,
      ∃ p : ({s : Nat // s ∈ T} → Fin (f y + 1)),
        (∀ n : Nat, ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + k + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          (∀ s : {s : Nat // s ∈ T}, g s.val = (p s).val)) ∧
        (∀ a b e : {s : Nat // s ∈ T},
          IsLeaf H a.val → IsLeaf H b.val →
          H.oneMeetLevel a.val b.val = e.val →
          K.oneMeetLevel (p a).val (p b).val = (p e).val) ∧
        (∀ a b c d e : {s : Nat // s ∈ T},
          a.val < b.val → c.val < d.val →
          IsLeaf H a.val → IsLeaf H b.val →
          IsLeaf H c.val → IsLeaf H d.val →
          H.twoMeetLevel a.val b.val c.val d.val = e.val →
          K.twoMeetLevel (p a).val (p b).val
            (p c).val (p d).val = (p e).val) := by
  classical
  obtain ⟨k, p, _hBounds, _hOrder, _hLeaf, _hOne, _hTwo,
      _hRange, _hEdge, hAll⟩ :=
    P.exists_cofinally_fixed_internal_gap_profile
      DH hx hy T hBetween
  let V := {s : Nat // s ∈ T}
  obtain ⟨j, hFull⟩ :=
    countableDiaryFiniteSupport_contains_finset DH T
  obtain ⟨g, Q, _hOld, hVal⟩ := hAll j
  have hSupported (s : V) :
      s.val ∈ countableDiaryFiniteSupport H (m + k + j) :=
    (countableDiaryFiniteSupport_mono H j (m + k + j)
      (by omega)) (hFull s.val s.property)
  refine ⟨k, p, hAll, ?_, ?_⟩
  · intro a b e ha hb hMeet
    have hExact :
        K.oneMeetLevel (g a.val) (g b.val) =
          g (H.oneMeetLevel a.val b.val) :=
      Q.1.leaf_oneMeet a.val b.val
        (hSupported a) (hSupported b) ha hb
    rw [hMeet, hVal a, hVal b, hVal e] at hExact
    exact hExact
  · intro a b c d e hab hcd ha hb hc hd hMeet
    have hExact :
        K.twoMeetLevel (g a.val) (g b.val)
          (g c.val) (g d.val) =
          g (H.twoMeetLevel a.val b.val c.val d.val) :=
      Q.1.leaf_twoMeet a.val b.val c.val d.val
        (hSupported a) (hSupported b)
        (hSupported c) (hSupported d)
        hab hcd ha hb hc hd
    rw [hMeet, hVal a, hVal b, hVal c, hVal d,
      hVal e] at hExact
    exact hExact

end DiaryLeafPriority
end ThreeUniformDiaries
