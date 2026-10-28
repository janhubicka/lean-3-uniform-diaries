import ThreeUniformDiaries.DiaryFiniteCanonicalCausalFullSourceEmbedding
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalProtectedOriginalPicture
import ThreeUniformDiaries.DiaryFiniteUniformProtectedFamilyCompletion

/-!
# Simultaneous exact canonical-flip copies inside one countable diary

The finite canonical sign-rooted causal graph is a genuine V/E pre-diary.
Each canonical SOURCE flip embeds into it as a full induced numerical-meet
copy; each entire source image is a protected finite S1/S2 picture.
Uniform relative completion chooses ONE dummy tail and ONE countable
RoleDiary for all these separately protected pictures.

This module composes those already checked interfaces. In the resulting
single countable diary, EVERY original canonical source flip has its
original induced edge/nonedge table and every nonmarker numerical singleton
and full ordered-pair meet is preserved by an explicit common-target map.

This does NOT make every target flip preserve a source copy. In particular
it does not assert universal flip absorption or the 3-uniform lower bound.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The common dummy-tail carrier used for all canonical source flips. -/
noncomputable def canonicalCausalCountableCarrier
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) (bits : Nat → Bool) :
    Ordered3Graph Nat :=
  finiteDummyTailCarrier
    (finiteCanonicalCausalMarkerGraph DA)
    (Fintype.card (FiniteCanonicalSignRootedVertex DA)) bits

/-- The actual source-to-countable numerical map, with the same
countable carrier for every canonical source-flip index. -/
noncomputable def canonicalCausalCountableSourceMap
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) (bits : Nat → Bool)
    (i : FiniteCanonicalFlipIndex A n) (u : Nat) : Nat :=
  onePassOldImage (canonicalCausalCountableCarrier DA bits)
    (finiteCanonicalSourceRankMap DA i u)

/-- All original canonical SOURCE flips have exact induced edge tables
and every nonmarker singleton/full numerical meet preserved
simultaneously inside ONE actual countable diary.

This theorem is strictly weaker than the still-open assertion that
every genuine flip of some fixed finite target absorbs the source. -/
theorem exists_countableDiary_simultaneousCanonicalSourceFlips
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ bits : Nat → Bool,
      RoleDiary
        (onePassRawTarget (canonicalCausalCountableCarrier DA bits)) ∧
      (∀ (i : FiniteCanonicalFlipIndex A n) (u v : Nat),
        3 ≤ u → u < n → 3 ≤ v → v < n →
        (onePassRawTarget (canonicalCausalCountableCarrier DA bits)).oneMeetLevel
          (canonicalCausalCountableSourceMap DA bits i u)
          (canonicalCausalCountableSourceMap DA bits i v) =
        canonicalCausalCountableSourceMap DA bits i
          (((finiteCanonicalSignRootedFamily DA).graph i).oneMeetLevel u v)) ∧
      (∀ (i : FiniteCanonicalFlipIndex A n) (a b c d : Nat),
        a < b → c < d →
        3 ≤ a → a < n → 3 ≤ b → b < n →
        3 ≤ c → c < n → 3 ≤ d → d < n →
        (onePassRawTarget (canonicalCausalCountableCarrier DA bits)).twoMeetLevel
          (canonicalCausalCountableSourceMap DA bits i a)
          (canonicalCausalCountableSourceMap DA bits i b)
          (canonicalCausalCountableSourceMap DA bits i c)
          (canonicalCausalCountableSourceMap DA bits i d) =
        canonicalCausalCountableSourceMap DA bits i
          (((finiteCanonicalSignRootedFamily DA).graph i).twoMeetLevel a b c d)) ∧
      (∀ (i : FiniteCanonicalFlipIndex A n) (a b c : Nat),
        a < b → b < c → c < n →
        ((onePassRawTarget (canonicalCausalCountableCarrier DA bits)).edge
          (canonicalCausalCountableSourceMap DA bits i a)
          (canonicalCausalCountableSourceMap DA bits i b)
          (canonicalCausalCountableSourceMap DA bits i c) ↔
          ((finiteCanonicalSignRootedFamily DA).graph i).edge a b c)) := by
  classical
  let H := finiteCanonicalCausalMarkerGraph DA
  let N := Fintype.card (FiniteCanonicalSignRootedVertex DA)
  let fam : FiniteCanonicalFlipIndex A n → Finset Nat :=
    fun i => finiteMeetImage n (finiteCanonicalSourceRankMap DA i)
  have hBound :
      ∀ (i : FiniteCanonicalFlipIndex A n) (u : Nat),
        u ∈ fam i → u < N := by
    intro i u hu
    change u ∈ finiteMeetImage n (finiteCanonicalSourceRankMap DA i) at hu
    rcases Finset.mem_image.mp hu with ⟨z,hz,rfl⟩
    exact finiteCanonicalSourceRankMap_lt_carrier DA i z
      (Finset.mem_Ico.mp hz).2
  have hMarked :
      ∀ (i : FiniteCanonicalFlipIndex A n) (u : Nat),
        3 ≤ u → u < n →
        finiteCanonicalSourceRankMap DA i u ∈
          finiteProtectedWithMarkers (fam i) := by
    intro i u hu3 hun
    change finiteCanonicalSourceRankMap DA i u ∈
      Finset.range 3 ∪ finiteMeetImage n (finiteCanonicalSourceRankMap DA i)
    apply Finset.mem_union.mpr
    exact Or.inr (Finset.mem_image.mpr
      ⟨u, Finset.mem_Ico.mpr ⟨hu3,hun⟩,rfl⟩)
  obtain ⟨bits,hDiary,hFamily,hEdge⟩ :=
    exists_countableDiary_completes_protectedFamily
      (finiteCanonicalCausalMarkerGraph_finitePrediary DA) fam
      (fun i => finiteCanonicalCausalMarkerGraph_original_protected_picture DA i)
      hBound
  refine ⟨bits,hDiary,?_,?_,?_⟩
  · intro i u v hu3 hun hv3 hvn
    let f := finiteCanonicalSourceRankMap DA i
    let C := canonicalCausalCountableCarrier DA bits
    have E := finiteCanonicalCausalMarkerGraph_sourceFiniteMeetEmbedding DA i
    change (onePassRawTarget C).oneMeetLevel
      (onePassOldImage C (f u)) (onePassOldImage C (f v)) =
      onePassOldImage C
        (f (((finiteCanonicalSignRootedFamily DA).graph i).oneMeetLevel u v))
    calc
      _ = onePassOldImage C (H.oneMeetLevel (f u) (f v)) :=
        (hFamily i).1 (f u) (f v)
          (hMarked i u hu3 hun) (hMarked i v hv3 hvn)
      _ = onePassOldImage C
            (f (((finiteCanonicalSignRootedFamily DA).graph i).oneMeetLevel u v)) :=
        congrArg (onePassOldImage C) (E.oneMeet u v hu3 hun hv3 hvn)
  · intro i a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
    let f := finiteCanonicalSourceRankMap DA i
    let C := canonicalCausalCountableCarrier DA bits
    have E := finiteCanonicalCausalMarkerGraph_sourceFiniteMeetEmbedding DA i
    change (onePassRawTarget C).twoMeetLevel
      (onePassOldImage C (f a)) (onePassOldImage C (f b))
      (onePassOldImage C (f c)) (onePassOldImage C (f d)) =
      onePassOldImage C
        (f (((finiteCanonicalSignRootedFamily DA).graph i).twoMeetLevel a b c d))
    calc
      _ = onePassOldImage C
            (H.twoMeetLevel (f a) (f b) (f c) (f d)) :=
        (hFamily i).2 (f a) (f b) (f c) (f d)
          (hMarked i a ha3 han) (hMarked i b hb3 hbn)
          (hMarked i c hc3 hcn) (hMarked i d hd3 hdn)
          (E.strictMono hab) (E.strictMono hcd)
      _ = onePassOldImage C
            (f (((finiteCanonicalSignRootedFamily DA).graph i).twoMeetLevel a b c d)) :=
        congrArg (onePassOldImage C)
          (E.twoMeet a b c d hab hcd
            ha3 han hb3 hbn hc3 hcn hd3 hdn)
  · intro i a b c hab hbc hcn
    let f := finiteCanonicalSourceRankMap DA i
    let C := canonicalCausalCountableCarrier DA bits
    have E := finiteCanonicalCausalMarkerGraph_sourceFiniteMeetEmbedding DA i
    have hcnN : f c < N :=
      finiteCanonicalSourceRankMap_lt_carrier DA i c hcn
    change (onePassRawTarget C).edge
      (onePassOldImage C (f a))
      (onePassOldImage C (f b))
      (onePassOldImage C (f c)) ↔
      ((finiteCanonicalSignRootedFamily DA).graph i).edge a b c
    exact (hEdge (f a) (f b) (f c) hcnN).trans
      (E.edge_iff a b c hab hbc hcn)

end DiaryLeafPriority
end ThreeUniformDiaries
