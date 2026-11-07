import ThreeUniformDiaries.DiaryUniformPointwiseBoundsFusion

/-!
# Track B: only leaf images need uniform bounds for countable diary fusion

The merged finite-front compactness theorem gives a full countable diary
embedding if there are independently admissible finite-stage support
maps satisfying ONE stage-independent image cap for every source vertex.

This module reduces that hypothesis to caps on source LEAVES ONLY.
Every vertex of a full diary lies before some genuine source leaf:
for a leaf use a later vertex; for a split use its V1/V2 witnesses.
Choose independent admissible finite-stage maps. A fixed source vertex
u is strictly below a fixed later witness leaf a(u). Once that leaf
appears in the selected finite support, all stages satisfy
 f_m(u) < f_m(a(u)) < leafCap(a(u)).
There are only finitely many earlier stages; take the supremum of
their chosen image values. Thus a single cap on all support vertices
exists, even though no finite stage maps were chosen coherently.

This is an exact refinement of the conditional countable-source
compactness gate. It DOES NOT construct bounded leaf images from
finite strong flip absorption, genericity, or arbitrary finite
prefix embeddings. No unrestricted countable-source flip property
is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every vertex of a countable full diary lies STRICTLY BEFORE
some genuine leaf. This needs V1/V2 witness nonemptiness at split
vertices, not an assumption that leaves are cofinal. -/
theorem RoleDiary.exists_later_leaf_after
    {H : Ordered3Graph Nat} (DH : RoleDiary H)
    (u : Nat) :
    ∃ a : Nat, u < a ∧ IsLeaf H a := by
  have hv3 : 3 ≤ u + 3 := by omega
  rcases DH.role_valid (u+3) hv3 with hLeaf | hOne | hTwo
  · exact ⟨u+3,by omega,hLeaf⟩
  · obtain ⟨a,b,ha,hb,hva,hvb,hm⟩ :=
      DH.one_split_witness (u+3) hOne
    exact ⟨a,by omega,ha⟩
  · obtain ⟨a,b,c,d,hab,hcd,ha,hb,hc,hd,hva,hvc,hm⟩ :=
      DH.two_split_witness (u+3) hTwo
    exact ⟨a,by omega,ha⟩

/-- Independently available finite-stage diary maps whose images of
selected source LEAVES have stage-independent caps already admit
stage-independent caps on EVERY vertex of the actual finite
leaf-meet support. No coherence or compactness is assumed in this
reduction; the result simply constructs the missing bound profile.

The cap of a source vertex u is the maximum of:
(1) the fixed cap of one later witness source leaf a(u);
(2) the finitely many images of u in the independently selected
    stages before that leaf was included, plus one.

Strict order on the finite stage support transfers the first cap
to the split vertex. Markers and capped meets need no extra cases. -/
theorem pointwiseBounds_of_uniform_leaf_bounds
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (F leafCap : Nat → Nat)
    (hStages : ∀ m : Nat,
      ∃ f : Nat → Nat,
        AdmissibleCofinalDiaryStage H K F m f ∧
        (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
          IsLeaf H u → f u < leafCap u)) :
    ∃ cap : Nat → Nat,
      ∀ m : Nat,
        ∃ f : Nat → Nat,
          AdmissibleCofinalDiaryStage H K F m f ∧
          (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
            f u < cap u) := by
  classical
  let maps : Nat → Nat → Nat :=
    fun m => Classical.choose (hStages m)
  have selected (m : Nat) :
      AdmissibleCofinalDiaryStage H K F m (maps m) ∧
      (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
        IsLeaf H u → maps m u < leafCap u) := by
    dsimp [maps]
    exact Classical.choose_spec (hStages m)
  let nextLeaf : Nat → Nat :=
    fun u => Classical.choose (DH.exists_later_leaf_after u)
  have nextLeaf_spec (u : Nat) :
      u < nextLeaf u ∧ IsLeaf H (nextLeaf u) := by
    dsimp [nextLeaf]
    exact Classical.choose_spec (DH.exists_later_leaf_after u)
  let cap : Nat → Nat :=
    fun u => max (leafCap (nextLeaf u))
      (((Finset.range (nextLeaf u+1)).sup
          (fun m => maps m u)) + 1)
  refine ⟨cap, ?_⟩
  intro m
  refine ⟨maps m,(selected m).1,?_⟩
  intro u hu
  let a := nextLeaf u
  have hua : u < a := (nextLeaf_spec u).1
  have haLeaf : IsLeaf H a := (nextLeaf_spec u).2
  by_cases hEarly : m < a + 1
  · have hm : m ∈ Finset.range (a+1) :=
      Finset.mem_range.mpr hEarly
    have hSup : maps m u ≤
        (Finset.range (a+1)).sup (fun k => maps k u) :=
      Finset.le_sup (f := fun k : Nat => maps k u) hm
    have hBound : maps m u < max (leafCap a)
        ((Finset.range (a+1)).sup (fun k => maps k u)+1) :=
      lt_of_lt_of_le (Nat.lt_succ_of_le hSup)
        (le_max_right _ _)
    change maps m u < cap u
    exact hBound
  · have ham : a < m := by omega
    have haSelected : a ∈ countableDiaryLeafPrefix H m :=
      (mem_countableDiaryLeafPrefix_iff H m a).mpr
        ⟨haLeaf.1,ham,haLeaf⟩
    have haSupport : a ∈ countableDiaryFiniteSupport H m :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H m) a haSelected
    have hOrdered : maps m u < maps m a :=
      (selected m).1.ordered u a hu haSupport hua
    have hLeafBound : maps m a < leafCap a :=
      (selected m).2 a haSupport haLeaf
    have hSmall : maps m u < leafCap a :=
      lt_trans hOrdered hLeafBound
    have hBound : maps m u < max (leafCap a)
        ((Finset.range (a+1)).sup (fun k => maps k u)+1) :=
      lt_of_lt_of_le hSmall (le_max_left _ _)
    change maps m u < cap u
    exact hBound

/-- The full countable embedding conclusion now requires only
uniform caps on SOURCE LEAF images at each finite stage, rather
than caps on all source split and marker images.

The caps are still an explicit UNPROVED input, and may not follow
from the strong finite absorber theorem. -/
theorem exists_fullDiaryEmbedding_of_uniform_leaf_bounds
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F leafCap : Nat → Nat)
    (hStages : ∀ m : Nat,
      ∃ f : Nat → Nat,
        AdmissibleCofinalDiaryStage H K F m f ∧
        (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
          IsLeaf H u → f u < leafCap u)) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  obtain ⟨cap,hEvery⟩ :=
    pointwiseBounds_of_uniform_leaf_bounds DH F leafCap hStages
  exact exists_fullDiaryEmbedding_of_pointwiseBounds
    DH DK F cap hEvery

end DiaryLeafPriority
end ThreeUniformDiaries
