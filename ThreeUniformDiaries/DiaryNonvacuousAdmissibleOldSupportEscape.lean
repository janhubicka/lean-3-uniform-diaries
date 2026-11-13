import ThreeUniformDiaries.DiaryAdmissibleOldStageBareGenericAvoidance
import ThreeUniformDiaries.DiaryGenericRefinementForcesOldSupportEscape

/-!
# Track C: nonvacuous support drift for ALL admissible next stages

English-first mathematical audit: janhubicka/3-uniform-diaries PR #340.

The new reserve-free Track C generic E5 obstruction produces a whole
UNORDERED induced generic copy J in the prescribed target true-leaf
range such that EVERY actual ADMISSIBLE next-stage map g whose new leaf
image lies in J sends the selected old leaf b beyond B.

This universal property is NONVACUOUS for full source/target RoleDiaries:
the independently checked finite-stage unavoidability theorem constructs
an actual RESERVED next stage in that SAME J. We transport its leaf-range
witnesses to the original F range, without changing any map image.

The source and target are countable role diaries; only ONE finite
source horizon m+1 is involved. No fixed new image through all later
horizons, AuxTypeRespecting generic refinement, or exact diary big
Ramsey degree is inferred.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For full source and target diaries, the reserve-free universal
old-support drift theorem has a genuine reserved next-stage witness
INSIDE THE SAME adversarial unordered generic J. -/
theorem RoleDiary.exists_nonvacuous_generic_refinement_forcing_admissible_old_support_escape
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (B M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      (∀ g : Nat → Nat,
        AdmissibleCofinalDiaryStage H K (fun t : Nat => F t) (m + 1) g →
        ∀ n : Nat, g m = J n → B ≤ g b) ∧
      (∃ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
        ∃ n : Nat, g m = J n) := by
  classical
  obtain ⟨J, hRange, hAll⟩ :=
    exists_generic_refinement_forcing_admissible_old_support_escape
      G F hFLeaf hm ha hb hab B M
  have hUniversal : Ordered3Graph.CountablyUniversal G.graph := by
    intro A
    obtain ⟨v, hvMono, hvEdge⟩ :=
      G.exists_countable_induced_embedding A
    let e : Ordered3Graph.Embedding A G.graph := {
      toFun := v
      strictMono := hvMono
      edge_iff := by
        intro x y z hxy hyz
        exact hvEdge x y z hxy hyz
    }
    exact ⟨e.asUnordered⟩
  have hJLeaf (t : Nat) : IsLeaf K (J t) :=
    (hRange t).2.1
  have hJInsideF (t : Nat) : ∃ i : Nat, J t = F i :=
    (hRange t).2.2
  obtain ⟨g, Q⟩ :=
    exists_independent_reserved_stage_in_universal_leaf_range
      DH DK G hUniversal J hJLeaf (m + 1)
  have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1) :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1, Nat.lt_succ_self m, hm⟩
  have hmSupport : m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) m hmSelected
  obtain ⟨n, hn⟩ := Q.1.leaf_range m hmSupport hm
  have QOriginal :
      ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g :=
    Q.weaken_leaf_range hJInsideF
  exact ⟨J, hRange, hAll, g, QOriginal, n, hn⟩

end DiaryLeafPriority
end ThreeUniformDiaries
