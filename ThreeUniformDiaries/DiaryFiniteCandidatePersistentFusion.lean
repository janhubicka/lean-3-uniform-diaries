import ThreeUniformDiaries.DiaryFiniteHorizonChoice
import ThreeUniformDiaries.DiaryLeafGeneratedStageCompatibility
import ThreeUniformDiaries.DiaryCountableCertifiedFusion

/-!
# Finite next-leaf image covers yield a non-circular countable fusion criterion

A stage is FINITELY PERSISTENT when it is admissible/reserved now,
and the SAME old supported images occur in some reserved realization
at every later FINITE horizon. This is a predicate entirely about
finite stages, not an assumed infinite embedding.

A genuinely finite set W of possible images for the NEXT source
leaf, covering arbitrarily long finite-horizon realizations while
retaining old images, allows one image v in W to persist at ALL finite
horizons. The finite-choice proof is the key: without the finite W
it fails, as the decreasing-Nat-sequence counterexample shows.

Selected leaf images determine all split-generator images. Hence
two long-horizon realizations agreeing on the old support and on
the new leaf automatically agree on the entire new generated
support. This promotes the next stage to finitely persistent.

Assuming such finite next-image covers at each finitely persistent
genuine leaf stage, certified countable fusion yields a full diary
embedding. This is a STRICTLY CONDITIONAL result. It does not
produce the required finite covers from hypergraph genericity,
finite absorption, or universal leaf ranges.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Explicit finite-stage persistence, without reference to any
infinite compatible family. At each later finite horizon there is
SOME (potentially different) reserved extension of the old support. -/
def PersistentReservedDiaryStage
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (f : Nat → Nat) : Prop :=
  ReservedDiaryStage H K F m f ∧
  ∀ n : Nat, ∃ g : Nat → Nat,
    ReservedDiaryStage H K F (m + n) g ∧
    CofinalDiaryStageCompatible H m f g

/-- Finite branching condition for the NEXT genuine source leaf m.
One fixed finite W covers the m-image of at least one compatible
reserved realization at each arbitrarily high finite horizon.
It neither asserts nor presupposes an infinite coherent branch. -/
def FiniteHorizonNextLeafCover
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (f : Nat → Nat) : Prop :=
  ∃ W : Finset Nat, ∀ n : Nat,
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      g m ∈ W

/-- A finite horizon-cover lets us choose a persistent successor.
Every target split image is determined by the old and new leaf
images, so no separate split-value boundedness is required. -/
theorem exists_persistent_reserved_successor_of_finite_cover
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (hCover : FiniteHorizonNextLeafCover H K F m f) :
    ∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g := by
  classical
  obtain ⟨W,hAllCover⟩ := hCover
  let R : Nat → Nat → Prop := fun v n =>
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      g m = v
  have hDown : ∀ v n k : Nat, k ≤ n → R v n → R v k := by
    intro v n k hkn
    rintro ⟨g,Q,hOld,hNew⟩
    refine ⟨g,Q.restrict (by omega),hOld,hNew⟩
  have hFiniteCover : ∀ n : Nat, ∃ v : Nat, v ∈ W ∧ R v n := by
    intro n
    obtain ⟨g,Q,hOld,hW⟩ := hAllCover n
    exact ⟨g m,hW,g,Q,hOld,rfl⟩
  obtain ⟨v,_hv,hStable⟩ :=
    finite_choice_persistent_of_downward W R hDown hFiniteCover
  obtain ⟨g0,Q0,hOld0,hVal0⟩ := hStable 0
  have hQ0 : ReservedDiaryStage H K F (m + 1) g0 := by
    simpa only [Nat.add_zero] using Q0
  have hPersistent : PersistentReservedDiaryStage H K F (m + 1) g0 := by
    refine ⟨hQ0,?_⟩
    intro n
    obtain ⟨gN,QN,hOldN,hValN⟩ := hStable n
    have hQN0 : ReservedDiaryStage H K F (m + 1) gN :=
      QN.restrict (by omega)
    have hEqualLeaves :
        ∀ u : Nat, u ∈ countableDiaryLeafPrefix H (m + 1) →
          g0 u = gN u := by
      intro u hu
      rw [countableDiaryLeafPrefix_succ_of_leaf H m hm] at hu
      rcases Finset.mem_insert.mp hu with hUm | hOldLeaf
      · subst u
        exact hVal0.trans hValN.symm
      · have huOld : u ∈ countableDiaryFiniteSupport H m :=
          mem_finiteLeafMeetSupport_leaf H
            (countableDiaryLeafPrefix H m) u hOldLeaf
        exact (hOld0 u huOld).trans (hOldN u huOld).symm
    have hSameSupport :=
      hQ0.1.eq_on_support_of_selected_leaves hQN0.1 hEqualLeaves
    refine ⟨gN,QN,?_⟩
    intro u hu
    exact (hSameSupport u hu).symm
  exact ⟨g0,hPersistent,hOld0⟩

/-- At nonleaf stages nothing changes in the support, and finite
persistence passes through unchanged. -/
theorem PersistentReservedDiaryStage.extend_of_not_leaf
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (P : PersistentReservedDiaryStage H K F m f)
    (hm : ¬ IsLeaf H m) :
    PersistentReservedDiaryStage H K F (m + 1) f := by
  refine ⟨P.1.extend_of_not_leaf hm,?_⟩
  intro n
  obtain ⟨g,Q,hCompatible⟩ := P.2 (n + 1)
  have hEq : m + (n + 1) = m + 1 + n := by omega
  refine ⟨g,by simpa only [hEq] using Q,?_⟩
  intro u hu
  have hOldSupport : u ∈ countableDiaryFiniteSupport H m := by
    rw [countableDiaryFiniteSupport_succ_of_not_leaf H m hm] at hu
    exact hu
  exact hCompatible u hOldSupport

/-- Marker-only initial stage is finitely persistent under the
previously verified independent reserved-stage existence theorem. -/
theorem persistent_reserved_marker_base
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (hUniversal : Ordered3Graph.CountablyUniversal U)
    (F : Ordered3Graph.UnorderedEmbedding U K)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t)) :
    PersistentReservedDiaryStage H K F 0 (fun u => u) := by
  refine ⟨ReservedDiaryStage.marker_base DH DK F,?_⟩
  intro n
  obtain ⟨g,Q⟩ :=
    exists_independent_reserved_stage_in_universal_leaf_range
      DH DK G hUniversal F hFleaf n
  refine ⟨g,Q,?_⟩
  intro u hu
  rw [countableDiaryFiniteSupport_zero_eq] at hu
  have hSmall : u < 3 := Finset.mem_range.mp hu
  have hCases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
  rcases hCases with rfl | rfl | rfl
  · exact Q.1.marker_zero
  · exact Q.1.marker_one
  · exact Q.1.marker_two

/-- A genuinely FINITE next-leaf cover at EVERY finitely persistent
leaf stage makes the checked certified-fusion theorem applicable.

The next-leaf cover is an independent, finite-horizon hypothesis.
It is NOT constructed here; the theorem is not unconditional
countable unavoidability or a disguised infinite-path assumption. -/
theorem exists_fullDiaryEmbedding_of_persistent_finite_covers
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (hUniversal : Ordered3Graph.CountablyUniversal U)
    (F : Ordered3Graph.UnorderedEmbedding U K)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t))
    (hFiniteCover : ∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        PersistentReservedDiaryStage H K F m f →
        FiniteHorizonNextLeafCover H K F m f) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  let C : CertifiedDiaryFusionData DH K F := {
    Safe := PersistentReservedDiaryStage H K F
    valid := by
      intro m f P
      exact P.1.1
    initial := by
      exact ⟨fun u => u,
        persistent_reserved_marker_base DH DK G hUniversal F hFleaf⟩
    next := by
      intro m f P
      by_cases hm : IsLeaf H m
      · obtain ⟨g,hPersistent,hCompatible⟩ :=
          exists_persistent_reserved_successor_of_finite_cover
            hm (hFiniteCover m hm f P)
        exact ⟨g,hPersistent,hCompatible⟩
      · exact ⟨f,P.extend_of_not_leaf hm,by intro u hu; rfl⟩
  }
  exact C.exists_full_embedding DK

end DiaryLeafPriority
end ThreeUniformDiaries
