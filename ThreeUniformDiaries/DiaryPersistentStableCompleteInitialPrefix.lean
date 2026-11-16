import ThreeUniformDiaries.DiaryPersistentInternalGapExactMeets

/-!
# Track A: an entire OLD-BOUNDED source prefix stabilizes through all finite horizons

Let f be a genuinely FINITELY PERSISTENT reserved support at source
horizon m, and let y be ANY already-supported source vertex.
The checked bounded-internal-gap profile theorem, with endpoints
the old marker 0 and y and with T consisting of ALL 0 < u < y,
produces ONE full finite image record, stable at every later source
horizon while the WHOLE old supported map f stays fixed.

A further cofinal-support cutoff places EVERY source vertex u <= y
inside ONE genuine later reserved stage. Choose its map h. EVERY
later source horizon has a real reserved map agreeing with this same
h at ALL u <= y, and with the old f throughout its whole support.

The base genuine stage certifies on this ONE stable literal prefix:
strict order; actual leaf/one-split/two-split roles; original F-range
for all genuine leaves; induced E5 edges AND nonedges on ALL triples;
exact NUMERICAL S1 singleton and S2 full pair meets for all genuine
source leaves in the prefix. These are actual stage obligations, not
inferred from bare inducedness or finite genericity.

CRITICAL: a NEW source leaf m normally lies to the RIGHT of all old
supported source positions y, and hence need not fall into ANY such
fixed old-bounded interval. Its numerical image can still escape.
This lemma does not produce a persistent new leaf, a full coherent
countable family, or countable diary unavoidability.

English-first proof:
  3-uniform-diaries/notes/track_a_persistent_complete_bounded_prefix_20261116.md
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For any genuine finitely persistent reserved OLD source stage f
and any already-supported source vertex y, the ENTIRE source
initial interval [0,y] has ONE strictly ordered, induced,
role-preserving, numerical-S1/S2-exact image map h.

The same h on ALL u <= y occurs in actual reserved full source stages
at EVERY future finite horizon m+k+n, with LITERAL agreement on the
entire original finite support S_m. The target prefix images are
bounded by f(y), but no new source leaf beyond old y is bounded.

Only the genuine source full RoleDiary and actual persistent
reserved-stage hypothesis are assumed; no generic target range
or countable diary embedding existence is asserted. -/
theorem PersistentReservedDiaryStage.exists_stable_complete_initial_prefix_below_supported_vertex
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m y : Nat}
    (DH : RoleDiary H)
    (P : PersistentReservedDiaryStage H K F m f)
    (hy : y ∈ countableDiaryFiniteSupport H m) :
    ∃ (k : Nat) (h : Nat → Nat),
      h y = f y ∧
      (∀ u : Nat, u ≤ y → h u ≤ f y) ∧
      (∀ u v : Nat, u < v → v ≤ y → h u < h v) ∧
      (∀ u : Nat, u ≤ y → IsLeaf H u → IsLeaf K (h u)) ∧
      (∀ u : Nat, u ≤ y → IsOneSplit H u → IsOneSplit K (h u)) ∧
      (∀ u : Nat, u ≤ y → IsTwoSplit H u → IsTwoSplit K (h u)) ∧
      (∀ u : Nat, u ≤ y → IsLeaf H u →
        ∃ i : Nat, h u = F i) ∧
      (∀ a b c : Nat, a < b → b < c → c ≤ y →
        (H.edge a b c ↔ K.edge (h a) (h b) (h c))) ∧
      (∀ a b : Nat, a ≤ y → b ≤ y →
        IsLeaf H a → IsLeaf H b →
        K.oneMeetLevel (h a) (h b) = h (H.oneMeetLevel a b)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        a ≤ y → b ≤ y → c ≤ y → d ≤ y →
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        K.twoMeetLevel (h a) (h b) (h c) (h d) =
          h (H.twoMeetLevel a b c d)) ∧
      (∀ n : Nat, ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + k + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        (∀ u : Nat, u ≤ y → g u = h u)) := by
  classical
  have hZero : (0 : Nat) ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_marker
      H (countableDiaryLeafPrefix H m) 0 (by omega)
  let T : Finset Nat := Finset.Ioo 0 y
  have hBetween : ∀ s : Nat, s ∈ T → 0 < s ∧ s < y := by
    intro s hs
    exact Finset.mem_Ioo.mp hs
  obtain ⟨k, p, _hBounds, _hOrder, _hLeaf, _hOne, _hTwo,
      _hRange, _hEdge, hAll⟩ :=
    P.exists_cofinally_fixed_internal_gap_profile
      DH hZero hy T hBetween
  obtain ⟨l, hFull⟩ :=
    countableDiaryFiniteSupport_contains_finset
      DH (Finset.range (y + 1))
  obtain ⟨h, Qbase, hOldBase, hTbase⟩ := hAll l
  have hSupported (u : Nat) (hu : u ≤ y) :
      u ∈ countableDiaryFiniteSupport H (m + k + l) := by
    have hAtL : u ∈ countableDiaryFiniteSupport H l :=
      hFull u (Finset.mem_range.mpr (by omega))
    exact (countableDiaryFiniteSupport_mono H l (m + k + l)
      (by omega)) hAtL
  have hY : h y = f y := hOldBase y hy
  have hStable (n : Nat) :
      ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + (k + l) + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        (∀ u : Nat, u ≤ y → g u = h u) := by
    obtain ⟨g, Q, hOld, hT⟩ := hAll (l + n)
    have Q' : ReservedDiaryStage H K F (m + (k + l) + n) g := by
      have hEq : m + k + (l + n) = m + (k + l) + n := by omega
      simpa only [hEq] using Q
    refine ⟨g, Q', hOld, ?_⟩
    intro u hu
    by_cases huZero : u = 0
    · subst u
      exact (hOld 0 hZero).trans (hOldBase 0 hZero).symm
    by_cases huY : u = y
    · subst u
      exact (hOld y hy).trans (hOldBase y hy).symm
    have hUinT : u ∈ T :=
      Finset.mem_Ioo.mpr (by omega)
    let s : {s : Nat // s ∈ T} := ⟨u, hUinT⟩
    exact (hT s).trans (hTbase s).symm
  refine ⟨k + l, h, hY, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hStable⟩
  · intro u hu
    rcases lt_or_eq_of_le hu with hlt | heq
    · have hOrder : h u < h y :=
        Qbase.1.ordered u y (hSupported u hu)
          (hSupported y (by omega)) hlt
      rw [hY] at hOrder
      omega
    · simpa only [heq, hY] using le_refl (f y)
  · intro u v huv hvy
    exact Qbase.1.ordered u v (hSupported u (by omega))
      (hSupported v hvy) huv
  · intro u hu hLeaf
    exact Qbase.1.leaf_role u (hSupported u hu) hLeaf
  · intro u hu hOne
    exact Qbase.1.one_split_role u (hSupported u hu) hOne
  · intro u hu hTwo
    exact Qbase.1.two_split_role u (hSupported u hu) hTwo
  · intro u hu hLeaf
    exact Qbase.1.leaf_range u (hSupported u hu) hLeaf
  · intro a b c hab hbc hcy
    exact Qbase.1.induced_edge a b c
      (hSupported a (by omega)) (hSupported b (by omega))
      (hSupported c hcy) hab hbc
  · intro a b ha hb hLa hLb
    exact Qbase.1.leaf_oneMeet a b
      (hSupported a ha) (hSupported b hb) hLa hLb
  · intro a b c d hab hcd ha hb hc hd hLa hLb hLc hLd
    exact Qbase.1.leaf_twoMeet a b c d
      (hSupported a ha) (hSupported b hb)
      (hSupported c hc) (hSupported d hd)
      hab hcd hLa hLb hLc hLd

end DiaryLeafPriority
end ThreeUniformDiaries
