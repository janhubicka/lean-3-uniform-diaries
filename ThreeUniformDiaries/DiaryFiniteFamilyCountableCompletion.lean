import ThreeUniformDiaries.DiaryFiniteFamilyJointEmbedding
import ThreeUniformDiaries.DiaryFiniteDummyTailProtectedCompletion
import ThreeUniformDiaries.DiaryOnePassTargetLeafCones
import ThreeUniformDiaries.DiaryProtectedMixedTypeTransport

/-!
# A common countable completed diary for every finite family

The verified finite-family theorem builds ONE finite V/E pre-diary
with genuine induced numerical-meet embeddings of every listed
finite diary. The verified causal dummy-tail theorem extends this
finite V/E pre-diary to ONE global RolePrediary on Nat; its finite
prefix remains induced and preserves all original numerical meets.

For each finite input diary, the image of its nonmarker vertices
is a protected S1/S2 picture in the finite pre-diary. Dummy-tail
extension keeps that picture protected, and the already verified
relative one-pass theorem preserves its complete singleton/full
pair-meet data, including mixed split/leaf comparisons.

We prove that the composite ORIGINAL-DIARY -> FINITE PRE-DIARY ->
COUNTABLE TAIL -> ONE-PASS DIARY map is a genuine finite meet
embedding (strictly increasing, fixes 0/1/2, reflects edges and
nonedges and literal roles, preserves all numerical meets).

Crucially all embeddings share the SAME choice of dummy-tail bits
and the SAME countable RoleDiary output. This proves finite-family
countable joint embedding. It does NOT yield a finite diary target
or show that EVERY flip of a target absorbs a prescribed source.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A G : Ordered3Graph Nat}
variable {n k : Nat} {f : Nat → Nat}

/-- Any marked source vertex within a finite induced meet embedding
lands below the ambient finite pre-diary bound. The three markers
follow from fixed-marker fields, and all nonmarkers from hRange. -/
theorem FiniteMeetEmbedding.all_lt_of_nonmarker_lt
    (E : FiniteMeetEmbedding A G n f)
    (hk : 3 ≤ k)
    (hRange : ∀ u : Nat, 3 ≤ u → u < n → f u < k)
    (u : Nat) (hu : u < n) : f u < k := by
  by_cases hu3 : 3 ≤ u
  · exact hRange u hu3 hu
  · have hCases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases hCases with h0 | h1 | h2
    · subst u
      rw [E.marker_zero]
      omega
    · subst u
      rw [E.marker_one]
      omega
    · subst u
      rw [E.marker_two]
      omega

/-- A nonmarker source vertex belongs to the marked protected
image of a genuine finite meet embedding. -/
theorem FiniteMeetEmbedding.nonmarker_mem_protectedImage
    (E : FiniteMeetEmbedding A G n f)
    (u : Nat) (hu3 : 3 ≤ u) (hun : u < n) :
    f u ∈ finiteProtectedWithMarkers (finiteMeetImage n f) := by
  change f u ∈ Finset.range 3 ∪ finiteMeetImage n f
  apply Finset.mem_union.mpr
  right
  change f u ∈ (Finset.Ico 3 n).image f
  exact Finset.mem_image.mpr
    ⟨u, Finset.mem_Ico.mpr ⟨hu3,hun⟩,rfl⟩

/-- A supplied finite diary embedding into a finite V/E pre-diary
extends to the SAME source finite diary embedded inside a completed
countable diary, once a causal dummy-tail pre-diary has been chosen.
All induced edges, genuine roles and exact numerical meets survive. -/
theorem FiniteMeetEmbedding.through_countable_completion
    (PG : FiniteRolePrediaryBlock G k)
    (DA : FiniteRoleDiaryBlock A n)
    (E : FiniteMeetEmbedding A G n f)
    (hRange : ∀ u : Nat, 3 ≤ u → u < n → f u < k)
    (bits : Nat → Bool)
    (PT : RolePrediary (finiteDummyTailCarrier G k bits)) :
    FiniteMeetEmbedding A
      (onePassRawTarget (finiteDummyTailCarrier G k bits)) n
      (fun u => onePassOldImage (finiteDummyTailCarrier G k bits) (f u)) := by
  classical
  let T := finiteDummyTailCarrier G k bits
  let C := onePassRawTarget T
  let F := finiteMeetImage n f
  have hBoundImage : ∀ u : Nat, u ∈ F → u < k := by
    intro u hu
    change u ∈ (Finset.Ico 3 n).image f at hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    have hvBounds := Finset.mem_Ico.mp hv
    exact hRange v hvBounds.1 hvBounds.2
  have QG : FiniteProtectedMeetPicture G F :=
    E.protected_picture DA
  have QT : FiniteProtectedMeetPicture T F :=
    finiteDummyTail_preserves_protected_picture
      PG QG hBoundImage bits
  have hSmall := E.all_lt_of_nonmarker_lt
    PG.frame.length_ge_three hRange
  have hOld := onePassOldImage_strictMono T
  refine {
    strictMono := ?_
    marker_zero := ?_
    marker_one := ?_
    marker_two := ?_
    edge_iff := ?_
    leaf_iff := ?_
    oneSplit_iff := ?_
    twoSplit_iff := ?_
    oneMeet := ?_
    twoMeet := ?_
  }
  · intro u v huv
    exact hOld (E.strictMono huv)
  · change onePassOldImage T (f 0) = 0
    rw [E.marker_zero, onePassOldImage_zero T]
  · change onePassOldImage T (f 1) = 1
    rw [E.marker_one, onePassOldImage_one T]
  · change onePassOldImage T (f 2) = 2
    rw [E.marker_two, onePassOldImage_two T]
  · intro a b c hab hbc hcn
    change C.edge (onePassOldImage T (f a))
      (onePassOldImage T (f b))
      (onePassOldImage T (f c)) ↔ A.edge a b c
    calc
      C.edge (onePassOldImage T (f a))
          (onePassOldImage T (f b))
          (onePassOldImage T (f c)) ↔ T.edge (f a) (f b) (f c) :=
        onePassRawTarget_edge_image_iff T (f a) (f b) (f c)
      _ ↔ G.edge (f a) (f b) (f c) :=
        finiteDummyTailCarrier_finite_edge_iff
          PG.frame bits (f a) (f b) (f c) (hSmall c hcn)
      _ ↔ A.edge a b c := E.edge_iff a b c hab hbc hcn
  · intro u hu3 hun
    have hfu : f u < k := hRange u hu3 hun
    change IsLeaf C (onePassOldImage T (f u)) ↔ IsLeaf A u
    calc
      IsLeaf C (onePassOldImage T (f u)) ↔ IsLeaf T (f u) :=
        onePassRawTarget_old_leaf_iff T (f u)
      _ ↔ IsLeaf G (f u) :=
        finiteDummyTailCarrier_old_leaf_iff
          PG.frame bits (f u) hfu
      _ ↔ IsLeaf A u := E.leaf_iff u hu3 hun
  · intro u hu3 hun
    have hfu : f u < k := hRange u hu3 hun
    change IsOneSplit C (onePassOldImage T (f u)) ↔
      IsOneSplit A u
    calc
      IsOneSplit C (onePassOldImage T (f u)) ↔ IsOneSplit T (f u) :=
        onePassRawTarget_old_oneSplit_iff T (f u)
      _ ↔ IsOneSplit G (f u) :=
        finiteDummyTailCarrier_old_oneSplit_iff
          PG.frame bits (f u) hfu
      _ ↔ IsOneSplit A u := E.oneSplit_iff u hu3 hun
  · intro u hu3 hun
    have hfu : f u < k := hRange u hu3 hun
    change IsTwoSplit C (onePassOldImage T (f u)) ↔
      IsTwoSplit A u
    calc
      IsTwoSplit C (onePassOldImage T (f u)) ↔ IsTwoSplit T (f u) :=
        onePassRawTarget_old_twoSplit_iff T (f u)
      _ ↔ IsTwoSplit G (f u) :=
        finiteDummyTailCarrier_old_twoSplit_iff
          PG.frame bits (f u) hfu
      _ ↔ IsTwoSplit A u := E.twoSplit_iff u hu3 hun
  · intro u v hu3 hun hv3 hvn
    have hMemU := E.nonmarker_mem_protectedImage u hu3 hun
    have hMemV := E.nonmarker_mem_protectedImage v hv3 hvn
    have hComplete :=
      onePass_finiteProtectedWithMarkers_oneMeet
        PT QT (f u) (f v) hMemU hMemV
    have hTail := finiteDummyTailCarrier_old_oneMeet_exact
      PG.frame bits (f u) (f v)
      (hRange u hu3 hun) (hRange v hv3 hvn)
    have hSource := E.oneMeet u v hu3 hun hv3 hvn
    change C.oneMeetLevel (onePassOldImage T (f u))
        (onePassOldImage T (f v)) =
      onePassOldImage T (f (A.oneMeetLevel u v))
    calc
      C.oneMeetLevel (onePassOldImage T (f u))
          (onePassOldImage T (f v)) =
          onePassOldImage T (T.oneMeetLevel (f u) (f v)) := hComplete
      _ = onePassOldImage T (G.oneMeetLevel (f u) (f v)) :=
        congrArg (onePassOldImage T) hTail
      _ = onePassOldImage T (f (A.oneMeetLevel u v)) :=
        congrArg (onePassOldImage T) hSource
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
    have hMemA := E.nonmarker_mem_protectedImage a ha3 han
    have hMemB := E.nonmarker_mem_protectedImage b hb3 hbn
    have hMemC := E.nonmarker_mem_protectedImage c hc3 hcn
    have hMemD := E.nonmarker_mem_protectedImage d hd3 hdn
    have hComplete :=
      onePass_finiteProtectedWithMarkers_twoMeet PT QT
        (f a) (f b) (f c) (f d)
        hMemA hMemB hMemC hMemD
        (E.strictMono hab) (E.strictMono hcd)
    have hTail := finiteDummyTailCarrier_old_twoMeet_exact
      PG.frame bits (f a) (f b) (f c) (f d)
      (hRange a ha3 han) (hRange b hb3 hbn)
      (hRange c hc3 hcn) (hRange d hd3 hdn)
    have hSource := E.twoMeet a b c d hab hcd
      ha3 han hb3 hbn hc3 hcn hd3 hdn
    change C.twoMeetLevel
        (onePassOldImage T (f a)) (onePassOldImage T (f b))
        (onePassOldImage T (f c)) (onePassOldImage T (f d)) =
      onePassOldImage T (f (A.twoMeetLevel a b c d))
    calc
      C.twoMeetLevel
          (onePassOldImage T (f a)) (onePassOldImage T (f b))
          (onePassOldImage T (f c)) (onePassOldImage T (f d)) =
          onePassOldImage T
            (T.twoMeetLevel (f a) (f b) (f c) (f d)) := hComplete
      _ = onePassOldImage T
          (G.twoMeetLevel (f a) (f b) (f c) (f d)) :=
        congrArg (onePassOldImage T) hTail
      _ = onePassOldImage T (f (A.twoMeetLevel a b c d)) :=
        congrArg (onePassOldImage T) hSource

/-- A single COUNTABLE COMPLETED DIARY jointly contains any
finite family of bounded finite diaries as induced, marker-role
and exact-meet preserving copies. Importantly, ONE causal
dummy-tail orientation and ONE one-pass completion are used for
the whole family, not separate targets for separate inputs. -/
theorem exists_countableDiary_for_finiteFamily
    (Ds : List FiniteDiaryInput) :
    ∃ C : Ordered3Graph Nat,
      RoleDiary C ∧
      ∀ D : FiniteDiaryInput, D ∈ Ds →
        ∃ f : Nat → Nat,
          FiniteMeetEmbedding D.graph C D.bound f := by
  obtain ⟨G,k,PG,hMaps⟩ :=
    exists_finiteFamily_meetEmbeddings Ds
  obtain ⟨bits,PT⟩ :=
    exists_finiteDummyTailCarrier_prediary PG
  let C := onePassRawTarget (finiteDummyTailCarrier G k bits)
  refine ⟨C, onePassRawTarget_isDiary PT, ?_⟩
  intro D hD
  obtain ⟨f,E,hRange⟩ := hMaps D hD
  refine ⟨fun u =>
    onePassOldImage (finiteDummyTailCarrier G k bits) (f u), ?_⟩
  exact E.through_countable_completion PG D.diary hRange bits PT

end DiaryLeafPriority
end ThreeUniformDiaries
