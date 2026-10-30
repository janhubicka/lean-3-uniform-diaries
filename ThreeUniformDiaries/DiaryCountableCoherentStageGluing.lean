import ThreeUniformDiaries.DiaryCountableCofinalFiniteSupports
import ThreeUniformDiaries.DiaryFiniteLeafMeetOnlySelectedLeaves
import ThreeUniformDiaries.DiaryPreembeddingSpec

/-!
# Gluing genuinely coherent finite diary support maps

The countable full diary H has an increasing exhaustive sequence
of finite full leaf-meet supports S_m. A family of finite-stage
maps φ_m:S_m -> K may or may not admit a countable limit:
merely having a copy of every S_m inside K is insufficient.

This module isolates the EXACT missing mathematical condition
for the countable-source unavoidability theorem. Assume all
stage maps are compatible ON OVERLAPS, preserve strict order,
all source role markers, all induced hyperedges/nonedges and
the actual singleton/full pair meets of source leaves.
Then their single coherent pointwise union exists and is a
genuine countable diary preembedding H -> K; moreover, unlike
an arbitrary preembedding, it preserves all induced triples.

We do NOT construct such a compatible family from the finite
flip property. In particular, this theorem cannot be misread
as proving unavoidability for arbitrary countable source diaries:
the relative finite extension/coherence condition is the
next open gate. No compactness or arbitrary free Boolean
orientation independence is postulated.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

private theorem cofinalDiaryStage_exists
    {H : Ordered3Graph Nat} (D : RoleDiary H) (u : Nat) :
    ∃ m : Nat, u ∈ countableDiaryFiniteSupport H m := by
  obtain ⟨m,hm⟩ :=
    countableDiaryFiniteSupport_eventually_contains D u
  exact ⟨m,hm m le_rfl⟩

/-- Choose ONE finite support stage containing the specified
source vertex. This is not required to be the least stage. -/
noncomputable def cofinalDiaryStageIndex
    {H : Ordered3Graph Nat} (D : RoleDiary H) (u : Nat) : Nat :=
  Classical.choose (cofinalDiaryStage_exists D u)

theorem cofinalDiaryStageIndex_mem
    {H : Ordered3Graph Nat} (D : RoleDiary H) (u : Nat) :
    u ∈ countableDiaryFiniteSupport H (cofinalDiaryStageIndex D u) := by
  unfold cofinalDiaryStageIndex
  exact Classical.choose_spec (cofinalDiaryStage_exists D u)

theorem cofinalDiaryStageIndex_mem_of_le
    {H : Ordered3Graph Nat} (D : RoleDiary H)
    (u m : Nat) (h : cofinalDiaryStageIndex D u ≤ m) :
    u ∈ countableDiaryFiniteSupport H m :=
  (countableDiaryFiniteSupport_mono
    H (cofinalDiaryStageIndex D u) m h)
      (cofinalDiaryStageIndex_mem D u)

/-- A genuine leaf in a generated finite full support is
necessarily one of the explicitly SELECTED prefix leaves.
The cap case of full 2-meets cannot create a new leaf. -/
theorem countableDiaryFiniteSupport_leaf_selected
    {H : Ordered3Graph Nat} (D : RoleDiary H)
    (m u : Nat)
    (hu : u ∈ countableDiaryFiniteSupport H m)
    (hLeaf : IsLeaf H u) :
    u ∈ countableDiaryLeafPrefix H m := by
  have hLeaves : ∀ z : Nat,
      z ∈ countableDiaryLeafPrefix H m → IsLeaf H z := by
    intro z hz
    exact ((mem_countableDiaryLeafPrefix_iff H m z).mp hz).2.2
  exact finiteLeafMeetSupport_leaf_mem_L
    D hLeaves hu hLeaf

/-- Data for a genuinely coherent compatible family of maps
defined on the ACTUAL nested finite leaf-meet supports of a
single countable full diary H. A map is supplied on all Nat
for convenience, but each stage's laws concern only S_m.
Compatibility is equality on the PREVIOUS support, not
independent existence of copies. -/
structure CoherentCofinalDiarySupportMaps
    {H : Ordered3Graph Nat} (D : RoleDiary H)
    (K : Ordered3Graph Nat) where
  map : Nat → Nat → Nat
  coherent : ∀ m n : Nat, m ≤ n →
    ∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
      map m u = map n u
  ordered : ∀ m u v : Nat,
    u ∈ countableDiaryFiniteSupport H m →
    v ∈ countableDiaryFiniteSupport H m →
    u < v → map m u < map m v
  marker_zero : ∀ m : Nat, map m 0 = 0
  marker_one : ∀ m : Nat, map m 1 = 1
  marker_two : ∀ m : Nat, map m 2 = 2
  leaf_role : ∀ m u : Nat,
    u ∈ countableDiaryFiniteSupport H m →
    IsLeaf H u → IsLeaf K (map m u)
  one_split_role : ∀ m u : Nat,
    u ∈ countableDiaryFiniteSupport H m →
    IsOneSplit H u → IsOneSplit K (map m u)
  two_split_role : ∀ m u : Nat,
    u ∈ countableDiaryFiniteSupport H m →
    IsTwoSplit H u → IsTwoSplit K (map m u)
  induced_edge : ∀ m a b c : Nat,
    a ∈ countableDiaryFiniteSupport H m →
    b ∈ countableDiaryFiniteSupport H m →
    c ∈ countableDiaryFiniteSupport H m →
    a < b → b < c →
    (H.edge a b c ↔
      K.edge (map m a) (map m b) (map m c))
  leaf_oneMeet : ∀ m a b : Nat,
    a ∈ countableDiaryFiniteSupport H m →
    b ∈ countableDiaryFiniteSupport H m →
    IsLeaf H a → IsLeaf H b →
    K.oneMeetLevel (map m a) (map m b) =
      map m (H.oneMeetLevel a b)
  leaf_twoMeet : ∀ m a b c d : Nat,
    a ∈ countableDiaryFiniteSupport H m →
    b ∈ countableDiaryFiniteSupport H m →
    c ∈ countableDiaryFiniteSupport H m →
    d ∈ countableDiaryFiniteSupport H m →
    a < b → c < d →
    IsLeaf H a → IsLeaf H b →
    IsLeaf H c → IsLeaf H d →
    K.twoMeetLevel (map m a) (map m b)
      (map m c) (map m d) =
      map m (H.twoMeetLevel a b c d)

namespace CoherentCofinalDiarySupportMaps

variable {H K : Ordered3Graph Nat} {D : RoleDiary H}

/-- The pointwise union of genuinely compatible finite-stage
support maps, with the witness stage fixed ONCE for each vertex. -/
noncomputable def limit
    (P : CoherentCofinalDiarySupportMaps D K) : Nat → Nat :=
  fun u => P.map (cofinalDiaryStageIndex D u) u

/-- The limit agrees exactly with ANY stage on the entirety
of its finite support. This is the critical coherence lemma,
and is false if each stage map is selected independently. -/
theorem limit_eq_stage
    (P : CoherentCofinalDiarySupportMaps D K)
    (m u : Nat)
    (hu : u ∈ countableDiaryFiniteSupport H m) :
    P.limit u = P.map m u := by
  let s := cofinalDiaryStageIndex D u
  let t := max s m
  have hs : u ∈ countableDiaryFiniteSupport H s :=
    cofinalDiaryStageIndex_mem D u
  have hS := P.coherent s t (le_max_left s m) u hs
  have hM := P.coherent m t (le_max_right s m) u hu
  change P.map s u = P.map m u
  exact hS.trans hM.symm

/-- Coherent finite stage maps glue into an actual countable
diary PREEMBEDDING with marker fixation, true role
preservation, strict order, induced leaf triples, and exact
singleton/full ordered-pair meets of ALL genuine source
leaves. No countable target diary assumptions are needed
to formulate this map property. -/
theorem limit_is_diaryPreembedding
    (P : CoherentCofinalDiarySupportMaps D K) :
    DiaryPreembeddingSpec H K P.limit := by
  classical
  refine {
    strictMono := ?_
    marker_zero := ?_
    marker_one := ?_
    marker_two := ?_
    leaf_role := ?_
    one_split_role := ?_
    two_split_role := ?_
    leaf_edge_iff := ?_
    leaf_one_meet := ?_
    leaf_two_meet := ?_
  }
  · intro u v huv
    let m := max (cofinalDiaryStageIndex D u)
      (cofinalDiaryStageIndex D v)
    have hu : u ∈ countableDiaryFiniteSupport H m :=
      cofinalDiaryStageIndex_mem_of_le D u m (by dsimp [m]; omega)
    have hv : v ∈ countableDiaryFiniteSupport H m :=
      cofinalDiaryStageIndex_mem_of_le D v m (by dsimp [m]; omega)
    rw [P.limit_eq_stage m u hu,P.limit_eq_stage m v hv]
    exact P.ordered m u v hu hv huv
  · have h0 : 0 ∈ countableDiaryFiniteSupport H 0 :=
      mem_finiteLeafMeetSupport_marker H
        (countableDiaryLeafPrefix H 0) 0 (by omega)
    calc
      P.limit 0 = P.map 0 0 := P.limit_eq_stage 0 0 h0
      _ = 0 := P.marker_zero 0
  · have h1 : 1 ∈ countableDiaryFiniteSupport H 0 :=
      mem_finiteLeafMeetSupport_marker H
        (countableDiaryLeafPrefix H 0) 1 (by omega)
    calc
      P.limit 1 = P.map 0 1 := P.limit_eq_stage 0 1 h1
      _ = 1 := P.marker_one 0
  · have h2 : 2 ∈ countableDiaryFiniteSupport H 0 :=
      mem_finiteLeafMeetSupport_marker H
        (countableDiaryLeafPrefix H 0) 2 (by omega)
    calc
      P.limit 2 = P.map 0 2 := P.limit_eq_stage 0 2 h2
      _ = 2 := P.marker_two 0
  · intro u hu
    change IsLeaf K (P.map (cofinalDiaryStageIndex D u) u)
    exact P.leaf_role (cofinalDiaryStageIndex D u) u
      (cofinalDiaryStageIndex_mem D u) hu
  · intro u hu
    change IsOneSplit K (P.map (cofinalDiaryStageIndex D u) u)
    exact P.one_split_role (cofinalDiaryStageIndex D u) u
      (cofinalDiaryStageIndex_mem D u) hu
  · intro u hu
    change IsTwoSplit K (P.map (cofinalDiaryStageIndex D u) u)
    exact P.two_split_role (cofinalDiaryStageIndex D u) u
      (cofinalDiaryStageIndex_mem D u) hu
  · intro a b c hab hbc ha hb hc
    let m := max (cofinalDiaryStageIndex D a)
      (max (cofinalDiaryStageIndex D b) (cofinalDiaryStageIndex D c))
    have hA : a ∈ countableDiaryFiniteSupport H m :=
      cofinalDiaryStageIndex_mem_of_le D a m (by dsimp [m]; omega)
    have hB : b ∈ countableDiaryFiniteSupport H m :=
      cofinalDiaryStageIndex_mem_of_le D b m (by dsimp [m]; omega)
    have hC : c ∈ countableDiaryFiniteSupport H m :=
      cofinalDiaryStageIndex_mem_of_le D c m (by dsimp [m]; omega)
    calc
      H.edge a b c ↔
          K.edge (P.map m a) (P.map m b) (P.map m c) :=
        P.induced_edge m a b c hA hB hC hab hbc
      _ ↔ K.edge (P.limit a) (P.limit b) (P.limit c) := by
        rw [P.limit_eq_stage m a hA,
            P.limit_eq_stage m b hB,
            P.limit_eq_stage m c hC]
  · intro a b ha hb
    let m := max (cofinalDiaryStageIndex D a)
      (cofinalDiaryStageIndex D b)
    have hA : a ∈ countableDiaryFiniteSupport H m :=
      cofinalDiaryStageIndex_mem_of_le D a m (by dsimp [m]; omega)
    have hB : b ∈ countableDiaryFiniteSupport H m :=
      cofinalDiaryStageIndex_mem_of_le D b m (by dsimp [m]; omega)
    have hMeet : H.oneMeetLevel a b ∈
        countableDiaryFiniteSupport H m := by
      by_cases hab : a = b
      · subst b
        simpa only [Ordered3Graph.oneMeetLevel_self] using hA
      · have hLA :=
          countableDiaryFiniteSupport_leaf_selected D m a hA ha
        have hLB :=
          countableDiaryFiniteSupport_leaf_selected D m b hB hb
        exact mem_finiteLeafMeetSupport_oneMeet H
          (countableDiaryLeafPrefix H m) a b hLA hLB hab
    calc
      K.oneMeetLevel (P.limit a) (P.limit b) =
          K.oneMeetLevel (P.map m a) (P.map m b) := by
        rw [P.limit_eq_stage m a hA,P.limit_eq_stage m b hB]
      _ = P.map m (H.oneMeetLevel a b) :=
        P.leaf_oneMeet m a b hA hB ha hb
      _ = P.limit (H.oneMeetLevel a b) :=
        (P.limit_eq_stage m (H.oneMeetLevel a b) hMeet).symm
  · intro a b c d hab hcd ha hb hc hd
    let m := max (max (cofinalDiaryStageIndex D a)
      (cofinalDiaryStageIndex D b))
      (max (cofinalDiaryStageIndex D c) (cofinalDiaryStageIndex D d))
    have hA : a ∈ countableDiaryFiniteSupport H m :=
      cofinalDiaryStageIndex_mem_of_le D a m (by dsimp [m]; omega)
    have hB : b ∈ countableDiaryFiniteSupport H m :=
      cofinalDiaryStageIndex_mem_of_le D b m (by dsimp [m]; omega)
    have hC : c ∈ countableDiaryFiniteSupport H m :=
      cofinalDiaryStageIndex_mem_of_le D c m (by dsimp [m]; omega)
    have hD : d ∈ countableDiaryFiniteSupport H m :=
      cofinalDiaryStageIndex_mem_of_le D d m (by dsimp [m]; omega)
    have hLA := countableDiaryFiniteSupport_leaf_selected D m a hA ha
    have hLB := countableDiaryFiniteSupport_leaf_selected D m b hB hb
    have hLC := countableDiaryFiniteSupport_leaf_selected D m c hC hc
    have hLD := countableDiaryFiniteSupport_leaf_selected D m d hD hd
    have hMeet : H.twoMeetLevel a b c d ∈
        countableDiaryFiniteSupport H m :=
      mem_finiteLeafMeetSupport_twoMeet H
        (countableDiaryLeafPrefix H m)
        a b c d hab hcd hLA hLB hLC hLD
    calc
      K.twoMeetLevel (P.limit a) (P.limit b)
          (P.limit c) (P.limit d) =
          K.twoMeetLevel (P.map m a) (P.map m b)
            (P.map m c) (P.map m d) := by
        rw [P.limit_eq_stage m a hA,P.limit_eq_stage m b hB,
            P.limit_eq_stage m c hC,P.limit_eq_stage m d hD]
      _ = P.map m (H.twoMeetLevel a b c d) :=
        P.leaf_twoMeet m a b c d
          hA hB hC hD hab hcd ha hb hc hd
      _ = P.limit (H.twoMeetLevel a b c d) :=
        (P.limit_eq_stage m (H.twoMeetLevel a b c d) hMeet).symm

/-- The coherent union in fact preserves and reflects ALL
increasing hyperedges and nonedges of the countable source
diary, not merely leaf triples, whenever the stage maps are
each fully induced on their finite source supports. -/
theorem limit_induced_all_triples
    (P : CoherentCofinalDiarySupportMaps D K) :
    ∀ a b c : Nat, a < b → b < c →
      (H.edge a b c ↔
        K.edge (P.limit a) (P.limit b) (P.limit c)) := by
  intro a b c hab hbc
  let m := max (cofinalDiaryStageIndex D a)
    (max (cofinalDiaryStageIndex D b) (cofinalDiaryStageIndex D c))
  have hA : a ∈ countableDiaryFiniteSupport H m :=
    cofinalDiaryStageIndex_mem_of_le D a m (by dsimp [m]; omega)
  have hB : b ∈ countableDiaryFiniteSupport H m :=
    cofinalDiaryStageIndex_mem_of_le D b m (by dsimp [m]; omega)
  have hC : c ∈ countableDiaryFiniteSupport H m :=
    cofinalDiaryStageIndex_mem_of_le D c m (by dsimp [m]; omega)
  calc
    H.edge a b c ↔
        K.edge (P.map m a) (P.map m b) (P.map m c) :=
      P.induced_edge m a b c hA hB hC hab hbc
    _ ↔ K.edge (P.limit a) (P.limit b) (P.limit c) := by
      rw [P.limit_eq_stage m a hA,
          P.limit_eq_stage m b hB,
          P.limit_eq_stage m c hC]

/-- If every finite-stage genuine source leaf also has its
image in a prescribed set F[Nat], the coherent limit keeps
ALL source leaf images in that same set. The stage-local
range witnesses may depend on the stage and vertex. -/
theorem limit_leaf_range
    (P : CoherentCofinalDiarySupportMaps D K)
    (F : Nat → Nat)
    (hRange : ∀ m u : Nat,
      u ∈ countableDiaryFiniteSupport H m →
      IsLeaf H u → ∃ t : Nat, P.map m u = F t) :
    ∀ u : Nat, IsLeaf H u →
      ∃ t : Nat, P.limit u = F t := by
  intro u hu
  let m := cofinalDiaryStageIndex D u
  obtain ⟨t,ht⟩ :=
    hRange m u (cofinalDiaryStageIndex_mem D u) hu
  exact ⟨t,ht⟩

end CoherentCofinalDiarySupportMaps
end DiaryLeafPriority
end ThreeUniformDiaries
