import ThreeUniformDiaries.DiaryCandidateFreshIncidenceGate
import ThreeUniformDiaries.DiaryReducedFiniteCandidateCriterion
import ThreeUniformDiaries.DiaryFiniteE2E3E5Gate
import ThreeUniformDiaries.DiaryPreembeddingMixedEdgeGate
import ThreeUniformDiaries.DiaryCountableInducedPreembeddingFullMeets

/-!
# Track D: exact E2/E3 criterion for inducing the entire countable diary

A genuine pre-embedding of countable full RoleDiary structures
already fixes markers, preserves vertex roles, leaves, all leaf
singleton/full pair numerical meets, and all E5 leaf triples.
The preceding verified-local E1/E4 reductions show E1 follows
from roles and E4 follows from E2 via the right one-split branch
bit and exact S1 singleton meet.

The five permitted edge shapes are EXHAUSTIVE in BOTH the source
and target full diaries. The target-to-source reflection needs
care: the map is strictly increasing and fixes markers, so
target marker images force identical source marker indices;
true source and target roles reflect by the already checked
role_iff theorem.

We therefore prove the full induced edge AND nonedge table is
equivalent to preserving only the E2 and E3 mixed branch families:
    edge(0,oneSplit,leaf)
    edge(twoSplit,leaf,leaf).
Neither family can be omitted without further geometry.
The already checked countable mixed-meet transfer upgrades this
induced pre-embedding to exact all-nonmarker one- and two-meets.

This is a precise *conditional* reduction, not a method for
constructing suitable relative next leaves or proving
countable source diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For an actual countable full-diary pre-embedding, the only
remaining independent mixed-edge tests are the E2 one-split/right
leaf bits and the E3 two-split/ordered-leaf-pair bits.

The equivalence includes edge REFLECTION (all nonedges):
it uses BOTH source and target E1–E5 permitted-edge classifications,
not merely the fact that every source edge has an allowed form. -/
theorem DiaryPreembeddingSpec.induced_iff_E2_E3
    {H K : Ordered3Graph Nat} {f : Nat → Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : DiaryPreembeddingSpec H K f) :
    ((∀ s b : Nat, IsOneSplit H s → IsLeaf H b → s < b →
        (H.edge 0 s b ↔ K.edge 0 (f s) (f b))) ∧
     (∀ s a b : Nat, IsTwoSplit H s →
        IsLeaf H a → IsLeaf H b → s < a → a < b →
        (H.edge s a b ↔ K.edge (f s) (f a) (f b)))) ↔
    (∀ a b c : Nat, a < b → b < c →
      (H.edge a b c ↔ K.edge (f a) (f b) (f c))) := by
  classical
  constructor
  · rintro ⟨hE2, hE3⟩
    have hMarker0 (x : Nat) (hx : f x = 0) : x = 0 := by
      by_contra hne
      have hpos : 0 < x := by omega
      have hmono := P.strictMono hpos
      rw [P.marker_zero, hx] at hmono
      omega
    have hMarker1 (x : Nat) (hx : f x = 1) : x = 1 := by
      rcases lt_trichotomy x 1 with hlt | heq | hgt
      · have hmono := P.strictMono hlt
        rw [hx, P.marker_one] at hmono
        omega
      · exact heq
      · have hmono := P.strictMono hgt
        rw [hx, P.marker_one] at hmono
        omega
    have hMarker2 (x : Nat) (hx : f x = 2) : x = 2 := by
      rcases lt_trichotomy x 2 with hlt | heq | hgt
      · have hmono := P.strictMono hlt
        rw [hx, P.marker_two] at hmono
        omega
      · exact heq
      · have hmono := P.strictMono hgt
        rw [hx, P.marker_two] at hmono
        omega
    have hNonmarker (x : Nat) (hx : 3 ≤ f x) : 3 ≤ x := by
      by_contra hnot
      have hx2 : x ≤ 2 := by omega
      have hmono : f x ≤ f 2 := P.strictMono.monotone hx2
      rw [P.marker_two] at hmono
      omega
    have hLeafRefl (x : Nat) (hx : IsLeaf K (f x)) :
        IsLeaf H x :=
      ((P.role_iff DH x (hNonmarker x hx.1)).1).mp hx
    have hOneRefl (x : Nat) (hx : IsOneSplit K (f x)) :
        IsOneSplit H x :=
      ((P.role_iff DH x (hNonmarker x hx.1)).2.1).mp hx
    have hTwoRefl (x : Nat) (hx : IsTwoSplit K (f x)) :
        IsTwoSplit H x :=
      ((P.role_iff DH x (hNonmarker x hx.1)).2.2).mp hx
    have hE4 (b c : Nat) (hbc : b < c)
        (hb : IsLeaf H b) (hc : IsLeaf H c) :
        (H.edge 1 b c ↔ K.edge 1 (f b) (f c)) ∧
        (H.edge 2 b c ↔ K.edge 2 (f b) (f c)) :=
      P.leaf_pair_marker_bits_of_oneSplit_bits DH DK hE2 b c hbc hb hc
    have hShape (a b c : Nat) (hab : a < b) (hbc : b < c)
        (hAllowed : PermittedDiaryEdge H a b c) :
        (H.edge a b c ↔ K.edge (f a) (f b) (f c)) := by
      rcases hAllowed with h1 | h2 | h3 | h4 | h5
      · rcases h1 with ⟨ha, hb, hc⟩
        rcases hb with hb | hb
        · subst a
          subst b
          simpa only [P.marker_zero, P.marker_one] using
            (P.marker_role_edge_bits DH c hc).1
        · subst a
          subst b
          simpa only [P.marker_zero, P.marker_two] using
            (P.marker_role_edge_bits DH c hc).2
      · rcases h2 with ⟨ha, hb, hc⟩
        subst a
        simpa only [P.marker_zero] using
          hE2 b c hb hc hbc
      · rcases h3 with ⟨ha, hb, hc⟩
        exact hE3 a b c ha hb hc hab hbc
      · rcases h4 with ⟨ha, hb, hc⟩
        rcases ha with ha | ha
        · subst a
          simpa only [P.marker_one] using (hE4 b c hbc hb hc).1
        · subst a
          simpa only [P.marker_two] using (hE4 b c hbc hb hc).2
      · rcases h5 with ⟨ha, hb, hc⟩
        exact P.leaf_edge_iff a b c hab hbc ha hb hc
    have hReflectPermitted (a b c : Nat)
        (hK : K.edge (f a) (f b) (f c)) :
        PermittedDiaryEdge H a b c := by
      rcases DK.permitted_edge (f a) (f b) (f c) hK with
        h1 | h2 | h3 | h4 | h5
      · rcases h1 with ⟨ha, hb, hc⟩
        have hba : b = 1 ∨ b = 2 := by
          rcases hb with hb | hb
          · exact Or.inl (hMarker1 b hb)
          · exact Or.inr (hMarker2 b hb)
        exact Or.inl ⟨hMarker0 a ha, hba, hNonmarker c hc⟩
      · rcases h2 with ⟨ha, hb, hc⟩
        exact Or.inr (Or.inl
          ⟨hMarker0 a ha, hOneRefl b hb, hLeafRefl c hc⟩)
      · rcases h3 with ⟨ha, hb, hc⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨hTwoRefl a ha, hLeafRefl b hb, hLeafRefl c hc⟩))
      · rcases h4 with ⟨ha, hb, hc⟩
        have haa : a = 1 ∨ a = 2 := by
          rcases ha with ha | ha
          · exact Or.inl (hMarker1 a ha)
          · exact Or.inr (hMarker2 a ha)
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨haa, hLeafRefl b hb, hLeafRefl c hc⟩)))
      · rcases h5 with ⟨ha, hb, hc⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hLeafRefl a ha, hLeafRefl b hb, hLeafRefl c hc⟩)))
    intro a b c hab hbc
    constructor
    · intro he
      exact (hShape a b c hab hbc
        (DH.permitted_edge a b c he)).mp he
    · intro he
      exact (hShape a b c hab hbc
        (hReflectPermitted a b c he)).mpr he
  · intro hInduced
    constructor
    · intro s b hs hb hsb
      have hspos : 0 < s := by
        have := hs.1
        omega
      have h := hInduced 0 s b hspos hsb
      simpa only [P.marker_zero] using h
    · intro s a b hs ha hb hsa hab
      exact hInduced s a b hsa hab

/-- The two independent mixed branch families E2 and E3
suffice not just for the full induced edge/nonedge table,
but also for ALL nonmarker numerical S1 and full-pair meets
of a countable full-diary pre-embedding.

This follows from the independently checked induced-preembedding
mixed-meet theorem; no extra convexity/closure condition is hidden. -/
theorem DiaryPreembeddingSpec.induced_and_all_meets_of_E2_E3
    {H K : Ordered3Graph Nat} {f : Nat → Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : DiaryPreembeddingSpec H K f)
    (hE2 : ∀ s b : Nat, IsOneSplit H s →
      IsLeaf H b → s < b →
      (H.edge 0 s b ↔ K.edge 0 (f s) (f b)))
    (hE3 : ∀ s a b : Nat, IsTwoSplit H s →
      IsLeaf H a → IsLeaf H b → s < a → a < b →
      (H.edge s a b ↔ K.edge (f s) (f a) (f b))) :
    (∀ a b c : Nat, a < b → b < c →
      (H.edge a b c ↔ K.edge (f a) (f b) (f c))) ∧
    (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
      K.oneMeetLevel (f u) (f v) = f (H.oneMeetLevel u v)) ∧
    (∀ a b c d : Nat, a < b → c < d →
      3 ≤ a → 3 ≤ c →
      K.twoMeetLevel (f a) (f b) (f c) (f d) =
        f (H.twoMeetLevel a b c d)) := by
  have hInduced :=
    (P.induced_iff_E2_E3 DH DK).mp ⟨hE2, hE3⟩
  have hInducedBack : ∀ a b c : Nat, a < b → b < c →
      (K.edge (f a) (f b) (f c) ↔ H.edge a b c) := by
    intro a b c hab hbc
    exact (hInduced a b c hab hbc).symm
  obtain ⟨hOne, hTwo⟩ :=
    P.all_numerical_meets_of_induced DH DK hInducedBack
  exact ⟨hInduced, hOne, hTwo⟩

end DiaryLeafPriority
end ThreeUniformDiaries
