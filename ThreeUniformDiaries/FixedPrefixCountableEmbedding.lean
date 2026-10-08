import ThreeUniformDiaries.FixedPrefixStage
import ThreeUniformDiaries.CountableInheritedEmbedding

/-!
# Countable inherited-gap embeddings fixing a prescribed initial segment

The original one-vertex-base construction does not suffice for Lemma Kiemb
when the prescribed initial segment I has more than one vertex. This
module starts instead with the literal identity stage on that common
initial segment, then repeatedly applies the previously verified
predecessor-relative finite extension.

The parent schedule is deliberately an explicit parameter. The separate
K_I enumeration must furnish that schedule before this result can
be applied to the actual universal branch hypergraph.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

variable (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
variable (n0 : Nat)
variable (hI : K.initialSegment n0 = G.graph.initialSegment n0)

/-- A predecessor index for each new vertex at source index n0+t. -/
abbrev PrefixParentSchedule := (t : Nat) → Fin (n0 + t)

/-- Coherent finite stages beginning with the identity on the common prefix. -/
noncomputable def fixedInheritedStages
    (parent : PrefixParentSchedule n0) :
    (t : Nat) → FiniteGenericStage G K (n0 + t)
  | 0 => G.fixedPrefixStage K n0 hI
  | t + 1 => (fixedInheritedStages parent t).extendInherited (parent t)

/-- Each successor stage fixes the images of all preceding source vertices. -/
theorem fixedInheritedStages_succ_old
    (parent : PrefixParentSchedule n0) (t : Nat) (i : Fin (n0 + t)) :
    ((G.fixedInheritedStages K n0 hI parent (t + 1)).image
      (Fin.castSucc i)).val =
      ((G.fixedInheritedStages K n0 hI parent t).image i).val := by
  exact FiniteGenericStage.extendInherited_old
    (G.fixedInheritedStages K n0 hI parent t) (parent t) i

/-- Every source vertex is eventually assigned a permanent target image. -/
theorem fixedInheritedStages_stable
    (parent : PrefixParentSchedule n0) (t u : Nat) (htu : t ≤ u)
    (i : Fin (n0 + t)) :
    ((G.fixedInheritedStages K n0 hI parent u).image
      ⟨i.val, by omega⟩).val =
      ((G.fixedInheritedStages K n0 hI parent t).image i).val := by
  induction u, htu using Nat.le_induction with
  | base => rfl
  | succ u hu ih =>
      calc
        ((G.fixedInheritedStages K n0 hI parent (u + 1)).image
          ⟨i.val, by omega⟩).val =
            ((G.fixedInheritedStages K n0 hI parent u).image
              ⟨i.val, by omega⟩).val := by
                exact G.fixedInheritedStages_succ_old K n0 hI parent u
                  ⟨i.val, by omega⟩
        _ = ((G.fixedInheritedStages K n0 hI parent t).image i).val := ih

/-- The countable map obtained by taking the stable images of every index.
Stage i+1 always contains source index i, including for n0=0. -/
noncomputable def fixedInheritedEmbedding
    (parent : PrefixParentSchedule n0) (i : Nat) : Nat :=
  ((G.fixedInheritedStages K n0 hI parent (i + 1)).image
    ⟨i, by omega⟩).val

/-- Any finite stage contains exactly the eventual images of its vertices,
regardless of whether the stage precedes or follows the defining stage. -/
theorem fixedInheritedEmbedding_at_stage
    (parent : PrefixParentSchedule n0) (t i : Nat)
    (hit : i < n0 + t) :
    ((G.fixedInheritedStages K n0 hI parent t).image
      ⟨i, hit⟩).val =
      G.fixedInheritedEmbedding K n0 hI parent i := by
  by_cases hti : t ≤ i + 1
  · have h := G.fixedInheritedStages_stable K n0 hI parent
        t (i + 1) hti ⟨i, hit⟩
    simpa only [fixedInheritedEmbedding] using h.symm
  · have hit' : i + 1 ≤ t := by omega
    have h := G.fixedInheritedStages_stable K n0 hI parent
        (i + 1) t hit' ⟨i, by omega⟩
    simpa only [fixedInheritedEmbedding] using h

/-- The countable map is literally the identity throughout the fixed prefix. -/
theorem fixedInheritedEmbedding_prefix
    (parent : PrefixParentSchedule n0) (i : Nat) (hi : i < n0) :
    G.fixedInheritedEmbedding K n0 hI parent i = i := by
  have h := G.fixedInheritedStages_stable K n0 hI parent
    0 (i + 1) (Nat.zero_le _) ⟨i, hi⟩
  simpa [fixedInheritedEmbedding, fixedInheritedStages,
    fixedPrefixStage] using h

/-- The union of the fixed-prefix stages is a strictly increasing
induced embedding, and still fixes the entire prescribed initial segment. -/
theorem fixedInheritedEmbedding_isEmbedding
    (parent : PrefixParentSchedule n0) :
    StrictMono (G.fixedInheritedEmbedding K n0 hI parent) ∧
      (∀ i : Nat, i < n0 →
         G.fixedInheritedEmbedding K n0 hI parent i = i) ∧
      ∀ a b c : Nat, a < b → b < c →
        (K.edge a b c ↔
          G.graph.edge
            (G.fixedInheritedEmbedding K n0 hI parent a)
            (G.fixedInheritedEmbedding K n0 hI parent b)
            (G.fixedInheritedEmbedding K n0 hI parent c)) := by
  refine ⟨?_, G.fixedInheritedEmbedding_prefix K n0 hI parent, ?_⟩
  · intro a b hab
    let S := G.fixedInheritedStages K n0 hI parent (b + 1)
    have h := S.mono
      (show (⟨a, by omega⟩ : Fin (n0 + (b + 1))) <
          (⟨b, by omega⟩ : Fin (n0 + (b + 1))) from hab)
    change (S.image ⟨a, by omega⟩).val <
      (S.image ⟨b, by omega⟩).val at h
    have ha : (S.image ⟨a, by omega⟩).val =
        G.fixedInheritedEmbedding K n0 hI parent a :=
      G.fixedInheritedEmbedding_at_stage K n0 hI parent (b + 1) a (by omega)
    have hb : (S.image ⟨b, by omega⟩).val =
        G.fixedInheritedEmbedding K n0 hI parent b :=
      G.fixedInheritedEmbedding_at_stage K n0 hI parent (b + 1) b (by omega)
    rw [ha, hb] at h
    exact h
  · intro a b c hab hbc
    let S := G.fixedInheritedStages K n0 hI parent (c + 1)
    have h := S.edge_iff
      ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ hab hbc
    have ha : (S.image ⟨a, by omega⟩).val =
        G.fixedInheritedEmbedding K n0 hI parent a :=
      G.fixedInheritedEmbedding_at_stage K n0 hI parent (c + 1) a (by omega)
    have hb : (S.image ⟨b, by omega⟩).val =
        G.fixedInheritedEmbedding K n0 hI parent b :=
      G.fixedInheritedEmbedding_at_stage K n0 hI parent (c + 1) b (by omega)
    have hc : (S.image ⟨c, by omega⟩).val =
        G.fixedInheritedEmbedding K n0 hI parent c :=
      G.fixedInheritedEmbedding_at_stage K n0 hI parent (c + 1) c (by omega)
    rw [ha, hb, hc] at h
    exact h

end GenericEnumerated3Graph
end ThreeUniformDiaries
