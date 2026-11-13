import ThreeUniformDiaries.CountableGenericEmbedding
import ThreeUniformDiaries.DiaryAnchoredGenericOldCutColourIff

/-!
# Track A: a colour-relative finite one-point extension yields a WHOLE generic copy

English-first adversarial audit: 3-uniform-diaries PR #339.

The missing existence problem is NOT solved by a good complete old-cut
colour recurring cofinally. We formulate the stronger, genuinely local
finite-stage hypothesis: EVERY already constructed strictly increasing
induced finite copy of the generic G whose images all have property C
admits a NEXT C-vertex above its entire finite range, with all prescribed
next-source-vertex positive AND negative edge tests.

Classical coherent recursion, not a compactness inference from merely
nonempty finite fibres, produces ONE actual increasing induced G selfcopy
whose entire range satisfies C. Compose with the ORIGINAL unordered
target leaf embedding F to obtain a monochromatic generic leaf range.
With an ACTUAL reserved successor anchor of that colour, the previously
kernel-checked anchored-and-generic-colour iff then gives arbitrary late
whole induced generic copies of ACTUAL compatible RESERVED immediate
next-leaf images, retaining the SAME old support.

The one-point extension premise is NOT derived from cofinality, finite
Ramsey, or the existence of any anchor. It need not hold for a bad
generic refinement or an arbitrary frozen old support. No all-future-
horizon persistent image or countable diary unavoidability is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A *finite-stage* colour-relative extension hypothesis.
Given ANY finite induced increasing embedding of the first n vertices
of actual generic G into G, entirely inside a vertex predicate C,
one can append ONE further C vertex above the current numerical bound
realizing EVERY prescribed new maximum-vertex E5 edge AND nonedge.

There is no bounded search algorithm or existence claim here; this
is an infinite schema of finite one-point extension assertions.
The empty stage is included. -/
def HasGenericColourOnePointExtensions
    (G : GenericEnumerated3Graph) (C : Nat → Prop) : Prop :=
  ∀ {n : Nat} (s : FiniteGenericStage G G.graph n),
    (∀ i : Fin n, C (s.image i).val) →
    ∃ v : Nat, s.bound ≤ v ∧ C v ∧
      ∀ i j : Fin n, i < j →
        (G.graph.edge i.val j.val n ↔
          G.graph.edge (s.image i).val (s.image j).val v)

/-- An actual finite induced generic stage with every selected
vertex in C. -/
structure FiniteColouredGenericStage
    (G : GenericEnumerated3Graph) (C : Nat → Prop) (n : Nat) where
  base : FiniteGenericStage G G.graph n
  good : ∀ i : Fin n, C (base.image i).val

namespace FiniteColouredGenericStage

/-- The empty finite stage is C-coloured vacuously. -/
def empty (G : GenericEnumerated3Graph) (C : Nat → Prop) :
    FiniteColouredGenericStage G C 0 where
  base := FiniteGenericStage.empty G G.graph
  good := by
    intro i
    exact Fin.elim0 i

/-- Append one C-coloured vertex without changing old images.
All internal source E5 edges and nonedges are preserved literally. -/
theorem exists_extend
    {G : GenericEnumerated3Graph}
    {C : Nat → Prop} {n : Nat}
    (s : FiniteColouredGenericStage G C n)
    (hExt : HasGenericColourOnePointExtensions G C) :
    ∃ s' : FiniteColouredGenericStage G C (n + 1),
      ∀ i : Fin n,
        (s'.base.image (Fin.castSucc i)).val =
          (s.base.image i).val := by
  classical
  let S := s.base
  obtain ⟨v, hv, hCv, hBits⟩ := hExt S s.good
  let image' := appendImage S.image hv
  let T : FiniteGenericStage G G.graph (n + 1) := {
    bound := v + 1
    image := image'
    mono := appendImage_strictMono S.image hv S.mono
    edge_iff := by
      intro i j k hij hjk
      have hi : i.val < n := by omega
      have hj : j.val < n := by omega
      by_cases hk : k.val < n
      · have hh :=
          S.edge_iff ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩
            hij hjk
        simpa [image', appendImage, hi, hj, hk] using hh
      · have hkval : k.val = n := by omega
        have hh :
            G.graph.edge i.val j.val n ↔
              G.graph.edge
                (S.image ⟨i.val, hi⟩).val
                (S.image ⟨j.val, hj⟩).val v :=
          hBits ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
        simpa [image', appendImage, hi, hj, hk, hkval] using hh
  }
  let next : FiniteColouredGenericStage G C (n + 1) := {
    base := T
    good := by
      intro i
      by_cases hi : i.val < n
      · have h := s.good ⟨i.val, hi⟩
        simpa [T, image', appendImage, hi] using h
      · have hiEq : i.val = n := by omega
        simpa [T, image', appendImage, hi, hiEq] using hCv
  }
  refine ⟨next, ?_⟩
  intro i
  change (image' (Fin.castSucc i)).val = (S.image i).val
  exact appendImage_old S.image hv i

end FiniteColouredGenericStage

/-- A coherent chain of increasing induced coloured finite stages. -/
noncomputable def finiteColourStages
    (G : GenericEnumerated3Graph) (C : Nat → Prop)
    (hExt : HasGenericColourOnePointExtensions G C) :
    (n : Nat) → FiniteColouredGenericStage G C n
  | 0 => FiniteColouredGenericStage.empty G C
  | n + 1 =>
      Classical.choose ((finiteColourStages G C hExt n).exists_extend hExt)

/-- Consecutive stages fix every previously selected actual index. -/
theorem finiteColourStages_succ_old
    (G : GenericEnumerated3Graph) (C : Nat → Prop)
    (hExt : HasGenericColourOnePointExtensions G C)
    (n : Nat) (i : Fin n) :
    ((finiteColourStages G C hExt (n + 1)).base.image
      (Fin.castSucc i)).val =
    ((finiteColourStages G C hExt n).base.image i).val := by
  exact (Classical.choose_spec
    ((finiteColourStages G C hExt n).exists_extend hExt)) i

/-- Old selected indices remain unchanged across arbitrary later stages. -/
theorem finiteColourStages_stable
    (G : GenericEnumerated3Graph) (C : Nat → Prop)
    (hExt : HasGenericColourOnePointExtensions G C)
    (n m : Nat) (hnm : n ≤ m) (i : Fin n) :
    ((finiteColourStages G C hExt m).base.image
      ⟨i.val, by omega⟩).val =
    ((finiteColourStages G C hExt n).base.image i).val := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      calc
        ((finiteColourStages G C hExt (m + 1)).base.image
          ⟨i.val, by omega⟩).val =
            ((finiteColourStages G C hExt m).base.image
              ⟨i.val, by omega⟩).val := by
                exact finiteColourStages_succ_old G C hExt m
                  ⟨i.val, by omega⟩
        _ = ((finiteColourStages G C hExt n).base.image i).val := ih

/-- The pointwise union of the coherent stages is a genuine map. -/
noncomputable def colourGenericEmbedding
    (G : GenericEnumerated3Graph) (C : Nat → Prop)
    (hExt : HasGenericColourOnePointExtensions G C)
    (i : Nat) : Nat :=
  ((finiteColourStages G C hExt (i + 1)).base.image
    (Fin.last i)).val

/-- Every finite selected vertex equals its stable limit value. -/
theorem colourGenericEmbedding_at_stage
    (G : GenericEnumerated3Graph) (C : Nat → Prop)
    (hExt : HasGenericColourOnePointExtensions G C)
    {i n : Nat} (hin : i < n) :
    ((finiteColourStages G C hExt n).base.image
      ⟨i, hin⟩).val =
    colourGenericEmbedding G C hExt i := by
  have hi := finiteColourStages_stable G C hExt
    (i + 1) n (by omega) (Fin.last i)
  simpa [colourGenericEmbedding] using hi

/-- The coherent limit embedding is strictly increasing in G indices. -/
theorem colourGenericEmbedding_strictMono
    (G : GenericEnumerated3Graph) (C : Nat → Prop)
    (hExt : HasGenericColourOnePointExtensions G C) :
    StrictMono (colourGenericEmbedding G C hExt) := by
  intro a b hab
  let S := finiteColourStages G C hExt (b + 1)
  have h := S.base.mono
    (show (⟨a, by omega⟩ : Fin (b + 1)) < Fin.last b from hab)
  change (S.base.image ⟨a, by omega⟩).val <
    (S.base.image (Fin.last b)).val at h
  simpa [colourGenericEmbedding, S,
    colourGenericEmbedding_at_stage G C hExt
      (show a < b + 1 by omega)] using h

/-- All generic edges and nonedges are preserved at the limit. -/
theorem colourGenericEmbedding_edge_iff
    (G : GenericEnumerated3Graph) (C : Nat → Prop)
    (hExt : HasGenericColourOnePointExtensions G C)
    (a b d : Nat) (hab : a < b) (hbd : b < d) :
    G.graph.edge a b d ↔
      G.graph.edge (colourGenericEmbedding G C hExt a)
        (colourGenericEmbedding G C hExt b)
        (colourGenericEmbedding G C hExt d) := by
  let S := finiteColourStages G C hExt (d + 1)
  have h := S.base.edge_iff
    ⟨a, by omega⟩ ⟨b, by omega⟩ (Fin.last d)
    (show a < b from hab) (show b < d from hbd)
  have ha : (S.base.image ⟨a, by omega⟩).val =
      colourGenericEmbedding G C hExt a :=
    colourGenericEmbedding_at_stage G C hExt (by omega)
  have hb : (S.base.image ⟨b, by omega⟩).val =
      colourGenericEmbedding G C hExt b :=
    colourGenericEmbedding_at_stage G C hExt (by omega)
  have hd : (S.base.image (Fin.last d)).val =
      colourGenericEmbedding G C hExt d :=
    colourGenericEmbedding_at_stage G C hExt (Nat.lt_succ_self d)
  rw [ha, hb, hd] at h
  exact h

/-- Every image vertex of the one coherent generic copy has C. -/
theorem colourGenericEmbedding_good
    (G : GenericEnumerated3Graph) (C : Nat → Prop)
    (hExt : HasGenericColourOnePointExtensions G C)
    (i : Nat) : C (colourGenericEmbedding G C hExt i) := by
  exact (finiteColourStages G C hExt (i + 1)).good (Fin.last i)

/-- A finite-stage one-point extension property produces an ENTIRE
increasing induced generic selfcopy in the prescribed colour class. -/
theorem exists_monochromatic_generic_selfcopy_of_onePointExtensions
    (G : GenericEnumerated3Graph) (C : Nat → Prop)
    (hExt : HasGenericColourOnePointExtensions G C) :
    ∃ u : Ordered3Graph.Embedding G.graph G.graph,
      ∀ i : Nat, C (u i) := by
  let u : Ordered3Graph.Embedding G.graph G.graph := {
    toFun := colourGenericEmbedding G C hExt
    strictMono := colourGenericEmbedding_strictMono G C hExt
    edge_iff := by
      intro a b d hab hbd
      exact colourGenericEmbedding_edge_iff G C hExt a b d hab hbd
  }
  exact ⟨u, colourGenericEmbedding_good G C hExt⟩

/-- A genuine target leaf range F of the original generic G
contains a WHOLE monochromatic induced generic subcopy, provided
the corresponding index-colour predicate satisfies the finite
one-point extension property. Outer F need NOT be numerically
monotone in the target enumeration. -/
theorem exists_generic_leaf_subcopy_in_prescribed_colour_of_onePointExtensions
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ i : Nat, IsLeaf K (F i))
    (Cut : Nat)
    (c : Fin Cut → Fin Cut → Bool)
    (hExt : HasGenericColourOnePointExtensions G
      (fun i : Nat =>
        DiaryLowerBoundColors.singletonColour K Cut (F i) = c)) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      ∀ i : Nat,
        IsLeaf K (J i) ∧ (∃ j : Nat, J i = F j) ∧
        DiaryLowerBoundColors.singletonColour K Cut (J i) = c := by
  obtain ⟨u, hColour⟩ :=
    exists_monochromatic_generic_selfcopy_of_onePointExtensions
      G (fun i : Nat =>
        DiaryLowerBoundColors.singletonColour K Cut (F i) = c) hExt
  let J : Ordered3Graph.UnorderedEmbedding G.graph K :=
    F.comp u.asUnordered
  refine ⟨J, ?_⟩
  intro i
  change IsLeaf K (F (u i)) ∧
    (∃ j : Nat, F (u i) = F j) ∧
    DiaryLowerBoundColors.singletonColour K Cut (F (u i)) = c
  exact ⟨hFLeaf (u i), ⟨u i, rfl⟩, hColour i⟩

/-- Concrete anchored-colour consequence: finite one-point
generic richness + one ACTUAL reserved old-cut colour anchor
give arbitrarily late WHOLE generic cones of genuine compatible
reserved immediate next leaves, fixing all old supported images.
The condition DOES NOT imply later source-horizon persistence. -/
theorem exists_reserved_generic_successor_cones_of_anchor_and_onePointExtensions
    {H K : Ordered3Graph Nat} {m : Nat}
    (hm : IsLeaf H m)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ i : Nat, IsLeaf K (F i))
    (f : Nat → Nat)
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool)
    (hAnchor : ∃ v : Nat,
      HasCompatibleReservedNextLeaf H K F f m v ∧
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v = c)
    (hExt : HasGenericColourOnePointExtensions G
      (fun i : Nat =>
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (F i) = c)) :
    ∀ M : Nat,
      ∃ U : Ordered3Graph.UnorderedEmbedding G.graph K,
        ∀ i : Nat,
          M < U i ∧ IsLeaf K (U i) ∧
          (∃ j : Nat, U i = F j) ∧
          HasCompatibleReservedNextLeaf H K F f m (U i) := by
  obtain ⟨J, hJ⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_colour_of_onePointExtensions
      G K F hFLeaf (oldStageTailCut H m f) c hExt
  have hSpectrum :
      ∃ d : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        ∃ V : Ordered3Graph.UnorderedEmbedding G.graph K,
          (∀ i : Nat,
            IsLeaf K (V i) ∧
            (∃ j : Nat, V i = F j) ∧
            DiaryLowerBoundColors.singletonColour K
              (oldStageTailCut H m f) (V i) = d) ∧
          (∃ v : Nat,
            HasCompatibleReservedNextLeaf H K F f m v ∧
            DiaryLowerBoundColors.singletonColour K
              (oldStageTailCut H m f) v = d) := by
    exact ⟨c, J, hJ, hAnchor⟩
  exact
    (whole_reserved_nextLeaf_generic_cones_iff_anchored_generic_oldCut_colour
      hm G).mp hSpectrum

end DiaryLeafPriority
end ThreeUniformDiaries
