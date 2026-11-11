import ThreeUniformDiaries.DiaryRelativeMultiColourTailObstruction
import ThreeUniformDiaries.DiarySingletonColourCofinalCone

/-!
# Track C: a cofinal COMPLETE mixed-colour fibre for every finite generic pattern

English proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #292

For any numerical target cut B and arbitrary Boolean pattern chi over ALL
target-ordered old pairs in the prescribed generic leaf range F[G] below B,
the verified actual generic relative extension theorem produces witnesses
of that whole pattern arbitrarily far out. The palette of complete mixed
singleton masks at B is finite. A downward finite-colour choice fixes ONE
complete mask recurring arbitrarily late while preserving ALL the bits
of the original prescribed leaf-only pattern.

The image F need not preserve order. Incompatible patterns on any actually
represented old target pair have DISJOINT stable complete-colour fibres.
This provides no relative E2/E3/marker/split control or persistence.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A *single fixed complete singleton colour* recurring with an entire
prescribed leaf-only incidence pattern on EVERY pair in the original
induced generic range below B, cofinally in source and target indices.

Nothing is asserted about prescribed marker/split vertices outside the
generic leaf range, nor about full diary future-horizon persistence. -/
def HasCofinalGenericPairPatternColour
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (B : Nat) (chi : Nat → Nat → Bool)
    (c : Fin B → Fin B → Bool) : Prop :=
  ∀ N M : Nat, ∃ t : Nat,
    N ≤ t ∧ M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
    DiaryLowerBoundColors.singletonColour K B (F t) = c ∧
    (∀ i j : Nat, F i < F j → F j < B →
      (K.edge (F i) (F j) (F t) ↔ chi (F i) (F j) = true))

/-- Every arbitrary complete positive/negative pattern on the finite
old generic leaf pairs below B has ONE COFINALLY INHABITED full mixed
singleton-colour class within the ORIGINAL prescribed generic range.

The entire pattern is enforced at each selected realization, not one
pair at a time. In particular nonedges are fully respected. -/
theorem exists_cofinal_generic_pair_pattern_full_colour
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hLeaves : ∀ t : Nat, IsLeaf K (F t))
    (B : Nat) (chi : Nat → Nat → Bool) :
    ∃ c : Fin B → Fin B → Bool,
      HasCofinalGenericPairPatternColour G K F B chi c := by
  classical
  let C := Fin B → Fin B → Bool
  let R : C → Nat → Prop := fun c M =>
    ∃ t : Nat, M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
      DiaryLowerBoundColors.singletonColour K B (F t) = c ∧
      (∀ i j : Nat, F i < F j → F j < B →
        (K.edge (F i) (F j) (F t) ↔ chi (F i) (F j) = true))
  have hDown : ∀ c : C, ∀ n k : Nat,
      k ≤ n → R c n → R c k := by
    intro c n k hkn
    rintro ⟨t, ht, hBt, hLeaf, hColour, hPattern⟩
    exact ⟨t, lt_of_le_of_lt hkn ht, hBt, hLeaf, hColour, hPattern⟩
  have hCover : ∀ M : Nat, ∃ c : C,
      c ∈ (Finset.univ : Finset C) ∧ R c M := by
    intro M
    obtain ⟨t, ht, hPattern⟩ :=
      exists_outer_generic_vertex_realizing_bounded_pair_pattern
        G K F B (max B M) chi
    have hMt : M < F t :=
      lt_of_le_of_lt (le_max_right B M) ht
    have hBt : B < F t :=
      lt_of_le_of_lt (le_max_left B M) ht
    exact ⟨DiaryLowerBoundColors.singletonColour K B (F t),
      Finset.mem_univ _, t, hMt, hBt, hLeaves t, rfl, hPattern⟩
  obtain ⟨c, _hc, hAll⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset C) R hDown hCover
  refine ⟨c, ?_⟩
  intro N M
  let L := max M ((Finset.range N).sup F)
  obtain ⟨t, ht, hBt, hLeaf, hColour, hPattern⟩ := hAll L
  have hIndex : N ≤ t := by
    by_contra hBad
    have htN : t < N := by omega
    have hBound : F t ≤ (Finset.range N).sup F :=
      Finset.le_sup (f := F) (Finset.mem_range.mpr htN)
    have hSupL : (Finset.range N).sup F ≤ L :=
      le_max_right _ _
    omega
  have hML : M ≤ L := le_max_left _ _
  exact ⟨t, hIndex, lt_of_le_of_lt hML ht,
    hBt, hLeaf, hColour, hPattern⟩

/-- Two cofinally inhabited full mixed singleton-colour fibres with
prescribed incidence patterns that disagree on an ACTUALLY PRESENT
old leaf pair below B must have DIFFERENT full colours.

The witness pair must lie in F[G] and below B; patterns differing only
outside the original generic leaf range need not be distinguishable. -/
theorem cofinal_generic_pair_pattern_colours_distinct_of_disagreement
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (B : Nat) (chi psi : Nat → Nat → Bool)
    (cChi cPsi : Fin B → Fin B → Bool)
    (hChi : HasCofinalGenericPairPatternColour G K F B chi cChi)
    (hPsi : HasCofinalGenericPairPatternColour G K F B psi cPsi)
    (i j : Nat) (hij : F i < F j) (hjB : F j < B)
    (hDisagree : chi (F i) (F j) ≠ psi (F i) (F j)) :
    cChi ≠ cPsi := by
  intro hEqual
  obtain ⟨p, _hpN, _hpM, _hpB, _hpLeaf, hColP, hPatP⟩ :=
    hChi 0 0
  obtain ⟨q, _hqN, _hqM, _hqB, _hqLeaf, hColQ, hPatQ⟩ :=
    hPsi 0 0
  have hEqualColour :
      DiaryLowerBoundColors.singletonColour K B (F p) =
        DiaryLowerBoundColors.singletonColour K B (F q) :=
    (hColP.trans hEqual).trans hColQ.symm
  have hSameEdge :
      (K.edge (F i) (F j) (F p) ↔
        K.edge (F i) (F j) (F q)) :=
    same_singletonColour_forces_same_old_pair_edge
      K B (F i) (F j) (F p) (F q) hij hjB hEqualColour
  have hSameBit :
      (chi (F i) (F j) = true ↔
        psi (F i) (F j) = true) :=
    (hPatP i j hij hjB).symm.trans
      (hSameEdge.trans (hPatQ i j hij hjB))
  have hBoolEq : chi (F i) (F j) = psi (F i) (F j) := by
    cases hP : chi (F i) (F j) <;>
      cases hQ : psi (F i) (F j) <;> simp_all
  exact hDisagree hBoolEq

end DiaryLeafPriority
end ThreeUniformDiaries
