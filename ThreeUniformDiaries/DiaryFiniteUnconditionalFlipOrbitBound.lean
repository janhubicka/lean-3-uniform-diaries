import ThreeUniformDiaries.DiaryFiniteFixedFlipSignature

/-!
# Unconditional fixed finite flip code, including the zero/one-leaf case

The fixed-source S2 witness signature of the preceding module
assumes one ordered pair of actual source leaves in order to
choose its global marker-one reference bit.

That assumption is eliminable. When the source has NO ordered
pair of leaves, S1 and S2 forbid all 1- and 2-splits. Hence
every genuine flip is already the same finite ordered graph,
by the verified positive-anchor induced-completion theorem
with vacuous split-anchor hypotheses.

A source-dependent reference pair (or an arbitrary dummy
pair in the degenerate case) therefore supplies ONE injection
for ALL finite diaries. The canonical finite edge-code orbit
has at most 2^(1 + #genuine two-splits) elements, with no
nondegeneracy or artificial independent-bit hypothesis.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- There is a bounded ordered pair of genuine source leaves. -/
def FiniteSourceHasLeafPair
    (A : Ordered3Graph Nat) (n : Nat) : Prop :=
  ∃ p : Nat × Nat,
    p.1 < p.2 ∧ p.2 < n ∧
    IsLeaf A p.1 ∧ IsLeaf A p.2

/-- A fixed source reference pair. The fallback (0,0) is
only used when no ordered source pair exists, in which case
the source has no genuine splits and the flip orbit is rigid. -/
noncomputable def finiteSourceLeafReference
    (A : Ordered3Graph Nat) (n : Nat) : Nat × Nat := by
  classical
  exact if h : FiniteSourceHasLeafPair A n then
    Classical.choose h
  else (0,0)

/-- In the nondegenerate case, the fixed reference is indeed
an ordered source leaf pair inside the finite diary frame. -/
theorem finiteSourceLeafReference_spec
    (A : Ordered3Graph Nat) (n : Nat)
    (h : FiniteSourceHasLeafPair A n) :
    (finiteSourceLeafReference A n).1 <
        (finiteSourceLeafReference A n).2 ∧
    (finiteSourceLeafReference A n).2 < n ∧
    IsLeaf A (finiteSourceLeafReference A n).1 ∧
    IsLeaf A (finiteSourceLeafReference A n).2 := by
  classical
  simpa only [finiteSourceLeafReference, dif_pos h] using
    (Classical.choose_spec h)

/-- If there are no two ordered source leaves, S1/S2 force
all genuine split sets to be empty, and two flips are literally
the same bounded hypergraph. No source reference pair is needed. -/
theorem finite_two_flips_eq_of_no_source_leaf_pair
    {A B C : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (FB : FiniteDiaryFlip A B n)
    (FC : FiniteDiaryFlip A C n)
    (hNo : ¬ FiniteSourceHasLeafPair A n) :
    B = C := by
  let K : FiniteDiaryFlip B C n := FB.symm.trans FC
  let Q : FiniteLeafPreembedding B C n n id :=
    K.identity_leafPreembedding
  have hOne :
      ∀ s : Nat, IsOneSplit B s →
        ∃ a : Nat, IsLeaf B a ∧ s < a ∧ a < n ∧
          B.edge 0 s a ∧ C.edge 0 s a := by
    intro s hsB
    have hsn : s < n := K.source_diary.prediary.oneSplit_lt s hsB
    have hsA : IsOneSplit A s :=
      ((FB.role_iff s hsB.1 hsn).2.1).mpr hsB
    obtain ⟨a,b,hab,hbn,ha,hb,_hsa,_hMeet⟩ :=
      finite_oneSplit_exists_ordered_leaf_witness DA s hsA
    exact False.elim (hNo ⟨(a,b),hab,hbn,ha,hb⟩)
  have hTwo :
      ∀ s : Nat, IsTwoSplit B s →
        ∃ a b : Nat, a < b ∧ b < n ∧
          IsLeaf B a ∧ IsLeaf B b ∧ s < a ∧
          B.edge s a b ∧ C.edge s a b := by
    intro s hsB
    have hsn : s < n := K.source_diary.prediary.twoSplit_lt s hsB
    have hsA : IsTwoSplit A s :=
      ((FB.role_iff s hsB.1 hsn).2.2).mpr hsB
    obtain ⟨a,b,c,d,hab,_hcd,_han,hbn,_hcn,_hdn,
      ha,hb,_hc,_hd,_hsa,_hsc,_hMeet⟩ :=
      DA.prediary.two_split_witness s hsA
        (DA.prediary.twoSplit_lt s hsA)
    exact False.elim (hNo ⟨(a,b),hab,hbn,ha,hb⟩)
  have hInduced :
      ∀ a b c : Nat, a < b → b < c → c < n →
        (C.edge a b c ↔ B.edge a b c) := by
    simpa only [id_eq] using
      (finite_leafPreembedding_induced_of_positive_split_anchors
        K.source_diary K.target_diary Q hOne hTwo)
  apply finiteDiary_graph_ext
  intro a b c
  constructor
  · intro hB
    obtain ⟨hab,hbc,_hc3,hcn⟩ :=
      K.source_diary.prediary.frame.edge_support a b c hB
    exact (hInduced a b c hab hbc hcn).mpr hB
  · intro hC
    obtain ⟨hab,hbc,_hc3,hcn⟩ :=
      K.target_diary.prediary.frame.edge_support a b c hC
    exact (hInduced a b c hab hbc hcn).mp hC

/-- One source-selected global marker reference (or a harmless
dummy in the rigid case), together with all fixed source S2
witness bits. This definition has NO leaf-count hypotheses. -/
noncomputable def finiteUnconditionalFlipSignature
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (T : Ordered3Graph Nat) :
    Bool × (FiniteTwoSplitIndex A n → Bool) :=
  finiteFixedFlipSignature DA
    (finiteSourceLeafReference A n).1
    (finiteSourceLeafReference A n).2 T

/-- For EVERY finite diary, the source-dependent signature
is injective on genuine flips. The case with no reference
leaf pair is handled by genuine diary rigidity, not by
silently postulating two nonexisting leaves. -/
theorem finiteUnconditionalFlipSignature_injective_on_flips
    {A B C : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (FB : FiniteDiaryFlip A B n)
    (FC : FiniteDiaryFlip A C n)
    (hSig : finiteUnconditionalFlipSignature DA B =
      finiteUnconditionalFlipSignature DA C) :
    B = C := by
  classical
  by_cases hPair : FiniteSourceHasLeafPair A n
  · have hRef := finiteSourceLeafReference_spec A n hPair
    exact finiteFixedFlipSignature_injective_on_flips
      DA (finiteSourceLeafReference A n).1
      (finiteSourceLeafReference A n).2
      hRef.1 hRef.2.1 hRef.2.2.1 hRef.2.2.2
      FB FC (by simpa only [finiteUnconditionalFlipSignature] using hSig)
  · exact finite_two_flips_eq_of_no_source_leaf_pair DA FB FC hPair

/-- Full unconditional orbit-size inequality, applying equally
to finite diaries with zero, one, or many genuine leaves.
The source orbit is the CANONICAL family of realisable flips,
not the exponentially redundant raw edge code table family. -/
theorem finiteCanonicalSourceFlipOrbit_card_bound_unconditional
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    Fintype.card
      {x : FiniteDiaryEdgeCode n //
        x ∈ finiteCanonicalSourceFlipCodes A n} ≤
      2 ^ (finiteTwoSplitCount A n + 1) := by
  classical
  let Orbit :=
    {x : FiniteDiaryEdgeCode n //
      x ∈ finiteCanonicalSourceFlipCodes A n}
  let Signature := Bool × (FiniteTwoSplitIndex A n → Bool)
  let code : Orbit → Signature :=
    fun x => finiteUnconditionalFlipSignature DA
      (finiteDiaryCodeGraph n x.val)
  have hInjective : Function.Injective code := by
    intro x y h
    apply Subtype.ext
    have Fx : FiniteDiaryFlip A (finiteDiaryCodeGraph n x.val) n :=
      (mem_finiteSourceFlipCodes_iff A n x.val).mp
        ((mem_finiteCanonicalSourceFlipCodes_iff A n x.val).mp x.property).1
    have Fy : FiniteDiaryFlip A (finiteDiaryCodeGraph n y.val) n :=
      (mem_finiteSourceFlipCodes_iff A n y.val).mp
        ((mem_finiteCanonicalSourceFlipCodes_iff A n y.val).mp y.property).1
    apply finiteCanonicalSourceFlipCodes_decode_injective A n
      x.val y.val x.property y.property
    exact finiteUnconditionalFlipSignature_injective_on_flips
      DA Fx Fy h
  have hBound : Fintype.card Orbit ≤ Fintype.card Signature :=
    Fintype.card_le_of_injective code hInjective
  have hSize :
      Fintype.card Signature =
        2 ^ (finiteTwoSplitCount A n + 1) := by
    dsimp [Signature, finiteTwoSplitCount]
    simp [Fintype.card_prod, pow_succ, mul_comm]
  simpa only [hSize] using hBound

end DiaryLeafPriority
end ThreeUniformDiaries
