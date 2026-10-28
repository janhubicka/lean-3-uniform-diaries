import ThreeUniformDiaries.DiaryFiniteCanonicalSourceRankMap
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalSourceLeafMeets
import ThreeUniformDiaries.DiaryFiniteInducedAllMeetTransport

/-!
# Complete meet embeddings of every original canonical flip branch

The actual finite causal sign-rooted graph is a verified finite
V/E pre-diary. Every original canonical flip remains an induced
increasing source branch and its full LEAF-ONLY numerical meets
are now preserved exactly, including all three S2 alternatives.

The existing finite induced all-meet transport theorem says this
is ENOUGH for every mixed split-containing numerical meet too:
the E1–E5 edge conditions and marker-prefix reflection determine
all missing singleton and auxiliary meet components.

We verify its exact hypotheses for the concrete sign-rooted
construction, first packaging a genuine FiniteLeafPreembedding
of each canonical SOURCE FLIP (not the unflipped original
source, whose E2/E3 incidences may have changed) and then
constructing a full FiniteMeetEmbedding into the SAME finite
causal pre-diary.

This is stronger than independently asserting the protected S1/S2
picture: all singleton and full pair-type numerical meets on ALL
source nonmarker vertices are preserved, including split/leaf
mixed comparisons. Each source nonmarker image is consequently
an ambient FiniteProtectedMeetPicture by the already validated
general theorem.

It does NOT prove finite S1/S2 for arbitrary cross-branch pairs
of the causal pre-diary, or that the resulting countable diary
absorbs every flip of one fixed finite target.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every actual canonical source flip is a GENUINE induced
leaf-preembedding into the final finite causal graph, with
all leaf singleton and full ordered-pair meets exactly preserved. -/
theorem finiteCanonicalCausalMarkerGraph_sourceLeafPreembedding
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n) :
    FiniteLeafPreembedding
      ((finiteCanonicalSignRootedFamily DA).graph i)
      (finiteCanonicalCausalMarkerGraph DA)
      n (Fintype.card (FiniteCanonicalSignRootedVertex DA))
      (finiteCanonicalSourceRankMap DA i) := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  let f := finiteCanonicalSourceRankMap DA i
  refine {
    strictMono := finiteCanonicalSourceRankMap_strictMono DA i
    marker_zero := finiteCanonicalSourceRankMap_marker DA i 0 (by omega)
    marker_one := finiteCanonicalSourceRankMap_marker DA i 1 (by omega)
    marker_two := finiteCanonicalSourceRankMap_marker DA i 2 (by omega)
    image_bound := finiteCanonicalSourceRankMap_lt_carrier DA i
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u hu3 hun
    have hTarget :=
      finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
        DA i u hu3 hun
    have hFlip := (F.flip i).role_iff u hu3 hun
    have hRoles :
        (IsLeaf G (f u) ↔ IsLeaf A u) ∧
        (IsOneSplit G (f u) ↔ IsOneSplit A u) ∧
        (IsTwoSplit G (f u) ↔ IsTwoSplit A u) := by
      simpa only [f,finiteCanonicalSourceRankMap_of_lt DA i u hun]
        using hTarget
    exact ⟨hRoles.1.trans hFlip.1,
      hRoles.2.1.trans hFlip.2.1,
      hRoles.2.2.trans hFlip.2.2⟩
  · intro a b c hab hbc hcn _ha _hb _hc
    have han : a < n := by omega
    have hbn : b < n := by omega
    have h := finiteCanonicalCausalMarkerGraph_branch_edge_iff
      DA i a b c hab hbc hcn
    simpa only [f,
      finiteCanonicalSourceRankMap_of_lt DA i a han,
      finiteCanonicalSourceRankMap_of_lt DA i b hbn,
      finiteCanonicalSourceRankMap_of_lt DA i c hcn] using h
  · intro u v hu3 hun hv3 hvn hu hv
    by_cases huv : u = v
    · subst v
      simp only [Ordered3Graph.oneMeetLevel_self]
    · have huA : IsLeaf A u :=
        ((F.flip i).role_iff u hu3 hun).1.mpr hu
      have hvA : IsLeaf A v :=
        ((F.flip i).role_iff v hv3 hvn).1.mpr hv
      let s := (F.graph i).oneMeetLevel u v
      have hsF : IsOneSplit (F.graph i) s :=
        finiteRoleDiary_s1_unordered
          (F.flip i).target_diary u v hun hvn hu hv huv
      have hsn : s < n :=
        (F.flip i).target_diary.prediary.oneSplit_lt s hsF
      have hsA : IsOneSplit A s :=
        ((F.flip i).role_iff s hsF.1 hsn).2.1.mpr hsF
      have hCap := (F.graph i).oneMeetLevel_le_min u v
      have hsu : s < u := by
        have hne : s ≠ u := by
          intro heq
          have hBad : IsOneSplit (F.graph i) u := by
            simpa only [heq] using hsF
          exact hu.2.1 hBad.2.1
        omega
      have hsv : s < v := by
        have hne : s ≠ v := by
          intro heq
          have hBad : IsOneSplit (F.graph i) v := by
            simpa only [heq] using hsF
          exact hv.2.1 hBad.2.1
        omega
      have hExact :=
        finiteCanonicalCausalMarkerGraph_original_proper_oneMeet_exact
          DA i s u v hsA hsn hsu hsv hun hvn huA hvA rfl
      simpa only [f,
        finiteCanonicalSourceRankMap_of_lt DA i u hun,
        finiteCanonicalSourceRankMap_of_lt DA i v hvn,
        finiteCanonicalSourceRankMap_of_lt DA i s hsn] using hExact
  · intro a b c d hab hcd ha3 han hb3 hbn
        hc3 hcn hd3 hdn ha hb hc hd
    have haA : IsLeaf A a :=
      ((F.flip i).role_iff a ha3 han).1.mpr ha
    have hbA : IsLeaf A b :=
      ((F.flip i).role_iff b hb3 hbn).1.mpr hb
    have hcA : IsLeaf A c :=
      ((F.flip i).role_iff c hc3 hcn).1.mpr hc
    have hdA : IsLeaf A d :=
      ((F.flip i).role_iff d hd3 hdn).1.mpr hd
    let m := (F.graph i).twoMeetLevel a b c d
    have hmBound : m < n := by
      have hCap := (F.graph i).twoMeetLevel_le_min a b c d
      dsimp [m]
      omega
    have hExact :=
      finiteCanonicalCausalMarkerGraph_original_leaf_twoMeets_exact
        DA i a b c d hab hcd hbn hdn haA hbA hcA hdA
    simpa only [f,
      finiteCanonicalSourceRankMap_of_lt DA i a han,
      finiteCanonicalSourceRankMap_of_lt DA i b hbn,
      finiteCanonicalSourceRankMap_of_lt DA i c hcn,
      finiteCanonicalSourceRankMap_of_lt DA i d hdn,
      finiteCanonicalSourceRankMap_of_lt DA i m hmBound] using hExact

/-- Exact induced-triple reflection holds for ALL source
triples, not just triples whose three source vertices are leaves. -/
theorem finiteCanonicalCausalMarkerGraph_sourceInduced
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (a b c : Nat)
    (hab : a < b) (hbc : b < c) (hcn : c < n) :
    (finiteCanonicalCausalMarkerGraph DA).edge
      (finiteCanonicalSourceRankMap DA i a)
      (finiteCanonicalSourceRankMap DA i b)
      (finiteCanonicalSourceRankMap DA i c) ↔
    ((finiteCanonicalSignRootedFamily DA).graph i).edge a b c := by
  have han : a < n := by omega
  have hbn : b < n := by omega
  have h := finiteCanonicalCausalMarkerGraph_branch_edge_iff
    DA i a b c hab hbc hcn
  simpa only [finiteCanonicalSourceRankMap_of_lt DA i a han,
    finiteCanonicalSourceRankMap_of_lt DA i b hbn,
    finiteCanonicalSourceRankMap_of_lt DA i c hcn] using h

/-- A genuine FINITE MEET EMBEDDING of every canonical source
flip into the SAME finite causal sign-rooted V/E pre-diary.
This includes all mixed split/leaf singleton and full pair
meets, not just leaf-only numerical meets. -/
theorem finiteCanonicalCausalMarkerGraph_sourceFiniteMeetEmbedding
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n) :
    FiniteMeetEmbedding
      ((finiteCanonicalSignRootedFamily DA).graph i)
      (finiteCanonicalCausalMarkerGraph DA)
      n (finiteCanonicalSourceRankMap DA i) := by
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  let f := finiteCanonicalSourceRankMap DA i
  let N := Fintype.card (FiniteCanonicalSignRootedVertex DA)
  have L : FiniteLeafPreembedding (F.graph i) G n N f :=
    finiteCanonicalCausalMarkerGraph_sourceLeafPreembedding DA i
  have hInduced :
      ∀ a b c : Nat, a < b → b < c → c < n →
        (G.edge (f a) (f b) (f c) ↔
          (F.graph i).edge a b c) :=
    finiteCanonicalCausalMarkerGraph_sourceInduced DA i
  have P : FiniteRolePrediaryBlock (F.graph i) n :=
    (F.flip i).target_diary.prediary
  have Q : FiniteRolePrediaryBlock G N :=
    finiteCanonicalCausalMarkerGraph_finitePrediary DA
  refine {
    strictMono := L.strictMono
    marker_zero := L.marker_zero
    marker_one := L.marker_one
    marker_two := L.marker_two
    edge_iff := hInduced
    leaf_iff := fun z hz3 hzn => (L.role_iff z hz3 hzn).1
    oneSplit_iff := fun z hz3 hzn => (L.role_iff z hz3 hzn).2.1
    twoSplit_iff := fun z hz3 hzn => (L.role_iff z hz3 hzn).2.2
    oneMeet := ?_
    twoMeet := ?_
  }
  · intro u v hu3 hun hv3 hvn
    exact finite_induced_all_oneMeet_preserved
      P Q L hInduced u v hu3 hun hv3 hvn
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
    exact finite_induced_all_twoMeet_preserved
      P Q L hInduced a b c d
      hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn

/-- The WHOLE nonmarker source image, including source split
vertices, is therefore an actual ambient protected S1/S2 picture
of the finite causal pre-diary. This follows from the stronger
full meet-embedding interface, not from an output S1/S2 assumption. -/
theorem finiteCanonicalCausalMarkerGraph_sourceProtectedPicture
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n) :
    FiniteProtectedMeetPicture
      (finiteCanonicalCausalMarkerGraph DA)
      (finiteMeetImage n (finiteCanonicalSourceRankMap DA i)) := by
  exact (finiteCanonicalCausalMarkerGraph_sourceFiniteMeetEmbedding DA i).protected_picture
    ((finiteCanonicalSignRootedFamily DA).flip i).target_diary

end DiaryLeafPriority
end ThreeUniformDiaries
