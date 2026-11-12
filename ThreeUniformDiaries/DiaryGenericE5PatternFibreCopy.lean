import ThreeUniformDiaries.DiaryGenericE5PatternFibreStep
import ThreeUniformDiaries.CountableGenericEmbedding

/-!
# Track C: an entire induced generic selfcopy in any finite old E5 pattern fibre

English proof/adversarial audit:
  janhubicka/3-uniform-diaries PR #299

The previously established finite extension lemma for DISJOINT
old A-pairs and already-selected generic-copy pairs is iterated
through a coherent chain of actual finite generic embeddings.
All selected images lie beyond the protected finite old set A
and realize the SAME prescribed complete positive/negative
old-pair pattern. The pointwise limit is one strictly increasing
induced selfembedding of the full enumerated generic hypergraph.

This is a positive **leaf-only E5** reservoir, not a diary-relative
S1/S2/E2/E3 candidate or a persistent countable diary embedding.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finite induced copy of the first n generic source vertices,
whose images all avoid the protected old set A and realize q on
EVERY ordered old pair. The generic finite-stage data retains
strict order and every internal edge/nonedge equivalence. -/
structure FiniteGenericE5FibreStage
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool) (n : Nat) where
  base : FiniteGenericStage G G.graph n
  aboveOld : ∀ i : Fin n, ∀ a : Nat, a ∈ A → a < (base.image i).val
  oldBits : ∀ i : Fin n, ∀ a b : Nat,
    a ∈ A → b ∈ A → a < b →
    (G.graph.edge a b (base.image i).val ↔ q a b = true)

namespace FiniteGenericE5FibreStage

/-- The empty stage has no image vertices and vacuously satisfies
the complete old-pattern invariant. -/
def empty (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool) :
    FiniteGenericE5FibreStage G A q 0 where
  base := FiniteGenericStage.empty G G.graph
  aboveOld := by
    intro i
    exact Fin.elim0 i
  oldBits := by
    intro i
    exact Fin.elim0 i

/-- A genuine next finite stage exists without moving old images.
The disjoint old-E5/internal-copy extension lemma supplies the
new vertex; the existing appendImage construction verifies order
and all internal edge/nonedge equivalences. -/
theorem exists_extend
    {G : GenericEnumerated3Graph}
    {A : Finset Nat} {q : Nat → Nat → Bool} {n : Nat}
    (s : FiniteGenericE5FibreStage G A q n) :
    ∃ s' : FiniteGenericE5FibreStage G A q (n + 1),
      ∀ i : Fin n,
        (s'.base.image (Fin.castSucc i)).val =
          (s.base.image i).val := by
  classical
  let S := s.base
  let B : Nat := max S.bound ((A.sup (fun x : Nat => x)) + 1)
  have hAB (a : Nat) (ha : a ∈ A) : a < B := by
    have hSup : a ≤ A.sup (fun x : Nat => x) :=
      Finset.le_sup (f := fun x : Nat => x) ha
    exact lt_of_lt_of_le (Nat.lt_succ_of_le hSup) (le_max_right _ _)
  have hOldB (i : Fin n) : (S.image i).val < B :=
    lt_of_lt_of_le (S.image i).isLt (le_max_left _ _)
  have hMono : StrictMono (fun i : Fin n => (S.image i).val) := by
    intro i j hij
    exact S.mono hij
  have hDisjoint (i : Fin n) : (S.image i).val ∉ A := by
    intro hi
    exact (lt_irrefl _) (s.aboveOld i (S.image i).val hi)
  obtain ⟨v, hBv, hOldPattern, hNewBits⟩ :=
    _root_.ThreeUniformDiaries.DiaryLeafPriority.GenericEnumerated3Graph.exists_extension_with_disjoint_old_pair_pattern
      G A q (fun i : Fin n => (S.image i).val)
      hMono hDisjoint B hAB hOldB
  have hv : S.bound ≤ v := (le_max_left _ _).trans hBv
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
          S.edge_iff ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk
        simpa [image', appendImage, hi, hj, hk] using hh
      · have hkval : k.val = n := by omega
        have hh :
            G.graph.edge i.val j.val n ↔
              G.graph.edge
                (S.image ⟨i.val, hi⟩).val
                (S.image ⟨j.val, hj⟩).val v := by
          exact (hNewBits ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij).symm
        simpa [image', appendImage, hi, hj, hk, hkval] using hh
  }
  let next : FiniteGenericE5FibreStage G A q (n + 1) := {
    base := T
    aboveOld := by
      intro i a ha
      by_cases hi : i.val < n
      · have h := s.aboveOld ⟨i.val, hi⟩ a ha
        simpa [T, image', appendImage, hi] using h
      · have h : a < v := lt_of_lt_of_le (hAB a ha) hBv
        simpa [T, image', appendImage, hi] using h
    oldBits := by
      intro i a b ha hb hab
      by_cases hi : i.val < n
      · have h := s.oldBits ⟨i.val, hi⟩ a b ha hb hab
        simpa [T, image', appendImage, hi] using h
      · have h := hOldPattern a b ha hb hab
        simpa [T, image', appendImage, hi] using h
  }
  refine ⟨next, ?_⟩
  intro i
  change (image' (Fin.castSucc i)).val = (S.image i).val
  exact appendImage_old S.image hv i

end FiniteGenericE5FibreStage

namespace GenericEnumerated3Graph

/-- Classical recursive chain of coherent finite generic E5-fibre
stages, retaining ALL earlier selected images. -/
noncomputable def e5FibreStages
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool) :
    (n : Nat) → FiniteGenericE5FibreStage G A q n
  | 0 => FiniteGenericE5FibreStage.empty G A q
  | n + 1 =>
      Classical.choose
        ((e5FibreStages G A q n).exists_extend)

/-- Exactly the same selected old images are used after each
successor stage. -/
theorem e5FibreStages_succ_old
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool)
    (n : Nat) (i : Fin n) :
    ((e5FibreStages G A q (n + 1)).base.image (Fin.castSucc i)).val =
      ((e5FibreStages G A q n).base.image i).val := by
  exact (Classical.choose_spec
    ((e5FibreStages G A q n).exists_extend)) i

/-- Every finite stage agrees literally with all later finite
stages on its selected vertices. -/
theorem e5FibreStages_stable
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool)
    (n m : Nat) (hnm : n ≤ m) (i : Fin n) :
    ((e5FibreStages G A q m).base.image ⟨i.val, by omega⟩).val =
      ((e5FibreStages G A q n).base.image i).val := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      calc
        ((e5FibreStages G A q (m + 1)).base.image
          ⟨i.val, by omega⟩).val =
            ((e5FibreStages G A q m).base.image
              ⟨i.val, by omega⟩).val := by
                exact e5FibreStages_succ_old G A q m
                  ⟨i.val, by omega⟩
        _ = ((e5FibreStages G A q n).base.image i).val := ih

/-- Pointwise union of the coherent finite generic E5-fibre stages. -/
noncomputable def e5FibreEmbedding
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool)
    (i : Nat) : Nat :=
  ((e5FibreStages G A q (i + 1)).base.image (Fin.last i)).val

/-- Every finite chosen image equals its final pointwise-union value. -/
theorem e5FibreEmbedding_at_stage
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool)
    {i n : Nat} (hin : i < n) :
    ((e5FibreStages G A q n).base.image ⟨i, hin⟩).val =
      e5FibreEmbedding G A q i := by
  have hi := e5FibreStages_stable G A q (i + 1) n
    (by omega) (Fin.last i)
  simpa [e5FibreEmbedding] using hi

/-- The limit map is strictly increasing. -/
theorem e5FibreEmbedding_strictMono
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool) :
    StrictMono (e5FibreEmbedding G A q) := by
  intro a b hab
  let S := e5FibreStages G A q (b + 1)
  have h := S.base.mono
    (show (⟨a, by omega⟩ : Fin (b + 1)) < Fin.last b from hab)
  change (S.base.image ⟨a, by omega⟩).val <
    (S.base.image (Fin.last b)).val at h
  simpa [e5FibreEmbedding, S,
    e5FibreEmbedding_at_stage G A q
      (show a < b + 1 by omega)] using h

/-- Every increasing source triple and every source nonedge is
preserved and reflected by the limit map. -/
theorem e5FibreEmbedding_edge_iff
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool)
    (a b c : Nat) (hab : a < b) (hbc : b < c) :
    G.graph.edge a b c ↔
      G.graph.edge (e5FibreEmbedding G A q a)
        (e5FibreEmbedding G A q b)
        (e5FibreEmbedding G A q c) := by
  let S := e5FibreStages G A q (c + 1)
  have h := S.base.edge_iff
    ⟨a, by omega⟩ ⟨b, by omega⟩ (Fin.last c)
    (show a < b from hab) (show b < c from hbc)
  have ha : (S.base.image ⟨a, by omega⟩).val =
      e5FibreEmbedding G A q a :=
    e5FibreEmbedding_at_stage G A q (by omega)
  have hb : (S.base.image ⟨b, by omega⟩).val =
      e5FibreEmbedding G A q b :=
    e5FibreEmbedding_at_stage G A q (by omega)
  have hc : (S.base.image (Fin.last c)).val =
      e5FibreEmbedding G A q c :=
    e5FibreEmbedding_at_stage G A q (Nat.lt_succ_self c)
  rw [ha, hb, hc] at h
  exact h

/-- The E5-fibre limit map's selected vertices are all strictly
after every protected old vertex and have the prescribed old-pair
positive/negative edge pattern. -/
theorem e5FibreEmbedding_old_pattern
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool)
    (i : Nat) :
    (∀ a : Nat, a ∈ A → a < e5FibreEmbedding G A q i) ∧
    (∀ a b : Nat, a ∈ A → b ∈ A → a < b →
      (G.graph.edge a b (e5FibreEmbedding G A q i) ↔
        q a b = true)) := by
  let S := e5FibreStages G A q (i + 1)
  constructor
  · intro a ha
    exact S.aboveOld (Fin.last i) a ha
  · intro a b ha hb hab
    exact S.oldBits (Fin.last i) a b ha hb hab

/-- Every finite old pair E5-pattern fibre contains an entire
strictly increasing, induced generic selfcopy after ANY input
threshold N. This is a COUNTABLE embedding in the generic leaf
reduct, not a full role/meet preserving diary embedding. -/
theorem exists_induced_generic_selfcopy_in_oldPair_fibre
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool) (N : Nat) :
    ∃ u : Ordered3Graph.Embedding G.graph G.graph,
      (∀ i : Nat, N < u i) ∧
      (∀ i a : Nat, a ∈ A → a < u i) ∧
      (∀ i a b : Nat, a ∈ A → b ∈ A → a < b →
        (G.graph.edge a b (u i) ↔ q a b = true)) := by
  classical
  let A' : Finset Nat := insert N A
  let u : Ordered3Graph.Embedding G.graph G.graph := {
    toFun := e5FibreEmbedding G A' q
    strictMono := e5FibreEmbedding_strictMono G A' q
    edge_iff := by
      intro a b c hab hbc
      exact e5FibreEmbedding_edge_iff G A' q a b c hab hbc
  }
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i
    exact (e5FibreEmbedding_old_pattern G A' q i).1
      N (Finset.mem_insert_self N A)
  · intro i a ha
    exact (e5FibreEmbedding_old_pattern G A' q i).1
      a (Finset.mem_insert_of_mem ha)
  · intro i a b ha hb hab
    exact (e5FibreEmbedding_old_pattern G A' q i).2
      a b (Finset.mem_insert_of_mem ha)
        (Finset.mem_insert_of_mem hb) hab

end GenericEnumerated3Graph
end DiaryLeafPriority
end ThreeUniformDiaries
