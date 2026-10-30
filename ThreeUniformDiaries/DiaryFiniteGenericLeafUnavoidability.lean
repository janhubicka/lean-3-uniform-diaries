import ThreeUniformDiaries.DiaryFiniteAbsorptionIntoCountable
import ThreeUniformDiaries.DiaryFiniteFamilyCountableCompletion
import ThreeUniformDiaries.DiaryUnconditionalPreembedding

/-!
# Genuine finite diary copies in the image of an arbitrary generic outer embedding

The final finite lower-bound application composes THREE INDEPENDENT
validated constructions:

1. Every finite full diary A admits a finite full strong flip
   absorber B. This is the unconditional result of PR #952.
2. A finite full diary B embeds with all numerical meets in SOME
   countable RoleDiary H (single-input case of the verified
   finite-family countable completion).
3. The unconditional positive-cut four-tail theorem produces a
   countable diary preembedding H -> K whose genuine source leaves
   all lie inside the image of a prescribed unordered embedding
   of the generic 3-hypergraph into the leaf hypergraph of K.

Restrict the countable preembedding to the embedded finite B.
The resulting map is a genuine finite LEAF preembedding of B into
K, including a real finite bound, even though global mixed
numerical meets need not be preserved. The induced finite
leaf-meet support of this image is a REAL finite flip of B.
By strong finite target-flip absorption it contains the original
unflipped A as an induced bounded full-meet copy. Transporting
this copy back to K yields a leaf preembedding of A, whose
entire finite induced ternary edge and NONEDGE table is correct,
and whose source leaf images are in the prescribed generic
outer embedding's range.

No unproved generic cut-zero orientation lemma, equality of
arbitrary mixed ambient meets, free Boolean cube, or false
claim that first-direction flip universality implies second-
direction target absorption is used.

This statement is the genuine FINITE source application of
the countable preembedding + finite flip-property lower-bound
argument. The exact final manuscript-level packaging as a
degree/lower-bound theorem remains separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- Full countable diary preembedding specifications preserve AND
reflect all three marker-defined roles, once the source is known
to satisfy genuine role coverage. The reflected directions are
not explicit fields of DiaryPreembeddingSpec, but follow from
the mutual incompatibility of the literal marker-edge codes. -/
theorem DiaryPreembeddingSpec.role_iff
    {H K : Ordered3Graph Nat} {θ : Nat → Nat}
    (DH : RoleDiary H) (P : DiaryPreembeddingSpec H K θ)
    (u : Nat) (hu3 : 3 ≤ u) :
    (IsLeaf K (θ u) ↔ IsLeaf H u) ∧
    (IsOneSplit K (θ u) ↔ IsOneSplit H u) ∧
    (IsTwoSplit K (θ u) ↔ IsTwoSplit H u) := by
  have hRoles := DH.role_valid u hu3
  refine ⟨?_,?_,?_⟩
  · constructor
    · intro hLeafK
      rcases hRoles with hLeafH | hOneH | hTwoH
      · exact hLeafH
      · exact False.elim (hLeafK.2.1 (P.one_split_role u hOneH).2.1)
      · exact False.elim (hLeafK.2.2 (P.two_split_role u hTwoH).2.2)
    · exact P.leaf_role u
  · constructor
    · intro hOneK
      rcases hRoles with hLeafH | hOneH | hTwoH
      · exact False.elim ((P.leaf_role u hLeafH).2.1 hOneK.2.1)
      · exact hOneH
      · exact False.elim ((P.two_split_role u hTwoH).2.1 hOneK.2.1)
    · exact P.one_split_role u
  · constructor
    · intro hTwoK
      rcases hRoles with hLeafH | hOneH | hTwoH
      · exact False.elim ((P.leaf_role u hLeafH).2.2 hTwoK.2.2)
      · exact False.elim ((P.one_split_role u hOneH).2.2 hTwoK.2.2)
      · exact hTwoH
    · exact P.two_split_role u

/-- A genuine full finite meet embedding A -> H followed by
a countable full diary preembedding H -> K gives a finite
bounded LEAF preembedding A -> K. The range bound is
θ(f n), which is explicit despite K being infinite.
This is NOT a claimed all-mixed-meet embedding into K. -/
theorem FiniteMeetEmbedding.comp_diaryPreembedding
    {A H K : Ordered3Graph Nat} {n : Nat}
    {f θ : Nat → Nat}
    (E : FiniteMeetEmbedding A H n f)
    (DH : RoleDiary H)
    (P : DiaryPreembeddingSpec H K θ) :
    FiniteLeafPreembedding A K n (θ (f n))
      (fun u => θ (f u)) := by
  let g : Nat → Nat := fun u => θ (f u)
  refine {
    strictMono := ?_
    marker_zero := ?_
    marker_one := ?_
    marker_two := ?_
    image_bound := ?_
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u v huv
    exact P.strictMono (E.strictMono huv)
  · change θ (f 0) = 0
    rw [E.marker_zero,P.marker_zero]
  · change θ (f 1) = 1
    rw [E.marker_one,P.marker_one]
  · change θ (f 2) = 2
    rw [E.marker_two,P.marker_two]
  · intro u hun
    exact P.strictMono (E.strictMono hun)
  · intro u hu3 hun
    have hfu3 : 3 ≤ f u := E.nonmarker_image_ge_three u hu3
    obtain ⟨hl,ho,ht⟩ := P.role_iff DH (f u) hfu3
    exact ⟨hl.trans (E.leaf_iff u hu3 hun),
      ho.trans (E.oneSplit_iff u hu3 hun),
      ht.trans (E.twoSplit_iff u hu3 hun)⟩
  · intro a b c hab hbc hcn ha hb hc
    have han : a < n := by omega
    have hbn : b < n := by omega
    have haH : IsLeaf H (f a) :=
      (E.leaf_iff a ha.1 han).mpr ha
    have hbH : IsLeaf H (f b) :=
      (E.leaf_iff b hb.1 hbn).mpr hb
    have hcH : IsLeaf H (f c) :=
      (E.leaf_iff c hc.1 hcn).mpr hc
    exact (P.leaf_edge_iff (f a) (f b) (f c)
      (E.strictMono hab) (E.strictMono hbc)
      haH hbH hcH).symm.trans
      (E.edge_iff a b c hab hbc hcn)
  · intro a b ha3 han hb3 hbn ha hb
    have haH : IsLeaf H (f a) :=
      (E.leaf_iff a ha3 han).mpr ha
    have hbH : IsLeaf H (f b) :=
      (E.leaf_iff b hb3 hbn).mpr hb
    calc
      K.oneMeetLevel (θ (f a)) (θ (f b)) =
          θ (H.oneMeetLevel (f a) (f b)) :=
        P.leaf_one_meet (f a) (f b) haH hbH
      _ = θ (f (A.oneMeetLevel a b)) :=
        congrArg θ (E.oneMeet a b ha3 han hb3 hbn)
  · intro a b c d hab hcd
      ha3 han hb3 hbn hc3 hcn hd3 hdn ha hb hc hd
    have haH : IsLeaf H (f a) :=
      (E.leaf_iff a ha3 han).mpr ha
    have hbH : IsLeaf H (f b) :=
      (E.leaf_iff b hb3 hbn).mpr hb
    have hcH : IsLeaf H (f c) :=
      (E.leaf_iff c hc3 hcn).mpr hc
    have hdH : IsLeaf H (f d) :=
      (E.leaf_iff d hd3 hdn).mpr hd
    calc
      K.twoMeetLevel (θ (f a)) (θ (f b))
          (θ (f c)) (θ (f d)) =
          θ (H.twoMeetLevel (f a) (f b) (f c) (f d)) :=
        P.leaf_two_meet (f a) (f b) (f c) (f d)
          (E.strictMono hab) (E.strictMono hcd)
          haH hbH hcH hdH
      _ = θ (f (A.twoMeetLevel a b c d)) :=
        congrArg θ (E.twoMeet a b c d hab hcd
          ha3 han hb3 hbn hc3 hcn hd3 hdn)

/-- Main FINITE unavoidability: for every source finite diary A,
every countable full diary K whose leaf graph contains an
unordered copy F of the enumerated generic hypergraph contains
an induced finite source copy A with ALL of its genuine leaves
inside the specified image F[G]. The source copy is strictly
increasing and marker/role/leaf-meet preserving.

All quantifiers are unconditional: no prescribed embedding
A -> K, auxiliary colouring or flip-injectivity certificate is
assumed. Only the user-specified unordered generic-to-leaf
embedding F is given. This result is stronger than just
finding a relational copy of the source leaf hypergraph,
because it also preserves all source leaf singleton and full
ordered-pair numerical meets. -/
theorem exists_finiteDiary_copy_in_generic_leaf_range
    {A K : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (DK : RoleDiary K) :
    ∃ (m : Nat) (g : Nat → Nat),
      FiniteLeafPreembedding A K n m g ∧
      (∀ a b c : Nat, a < b → b < c → c < n →
        (K.edge (g a) (g b) (g c) ↔ A.edge a b c)) ∧
      (∀ u : Nat, 3 ≤ u → u < n → IsLeaf A u →
        ∃ t, g u = F t) := by
  classical
  obtain ⟨B,k,DB,hAbs⟩ :=
    exists_finiteDiary_universal_flip_absorber DA
  let D : FiniteDiaryInput :=
    ⟨B,k,DB⟩
  obtain ⟨H,DH,hFamily⟩ :=
    exists_countableDiary_for_finiteFamily [D]
  obtain ⟨h,Eh⟩ :=
    hFamily D (by simp)
  have hB : FiniteMeetEmbedding B H k h := Eh
  obtain ⟨θ,Pθ,hLeafRange⟩ :=
    RoleDiary.exists_preembedding_into_leaf_range
      G K F hFleaf DH DK
  have PB :
      FiniteLeafPreembedding B K k (θ (h k))
        (fun v => θ (h v)) :=
    hB.comp_diaryPreembedding DH Pθ
  obtain ⟨g,PG,hInduced,hLeaves⟩ :=
    exists_induced_finite_source_in_countable_of_absorber_preembedding
      DA DB DK hAbs PB
  refine ⟨θ (h k),g,PG,hInduced,?_⟩
  intro u hu3 hun hu
  obtain ⟨v,hvk,hvLeaf,hgv⟩ :=
    hLeaves u hu3 hun hu
  have hhLeaf : IsLeaf H (h v) :=
    (hB.leaf_iff v hvLeaf.1 hvk).mpr hvLeaf
  obtain ⟨t,ht⟩ :=
    hLeafRange (h v) hhLeaf
  exact ⟨t,hgv.trans ht⟩

end DiaryLeafPriority
end ThreeUniformDiaries
