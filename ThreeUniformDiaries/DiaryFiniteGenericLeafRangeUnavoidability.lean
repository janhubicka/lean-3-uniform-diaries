import ThreeUniformDiaries.DiaryFiniteAbsorptionIntoCountable
import ThreeUniformDiaries.DiaryFiniteFamilyCountableCompletion
import ThreeUniformDiaries.DiaryUnconditionalPreembedding
import ThreeUniformDiaries.DiaryPreembeddingSpec

/-!
# Finite diary unavoidability inside the original generic leaf range

Given a finite source A and any unordered generic-to-leaf embedding
F into a countable full diary K, first choose A's finite strong
flip absorber B. Embed B into a countable full diary C, and obtain
the native ATR/four-tail diary preembedding theta:C -> K with
original source leaf images in the range of F.

Compose the finite meet embedding B -> C with theta. Recover role
reflection from finite role exhaustiveness, then apply the verified
finite absorber pullback through countable leaf preembeddings.
The result is an induced finite source copy A -> K, with exact
singleton and full ordered-pair leaf meets, all A leaves in F's
ORIGINAL range. Global mixed meets are deliberately NOT asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
open Ordered3Graph

/-- Forward preservation of all three exhaustive and disjoint
marker roles gives their exact equivalence on the source vertex. -/
theorem finite_role_equiv_of_role_preservation
    {H K : Ordered3Graph Nat} (f : Nat → Nat) (u : Nat)
    (hValid : IsLeaf H u ∨ IsOneSplit H u ∨ IsTwoSplit H u)
    (hLeaf : IsLeaf H u → IsLeaf K (f u))
    (hOne : IsOneSplit H u → IsOneSplit K (f u))
    (hTwo : IsTwoSplit H u → IsTwoSplit K (f u)) :
    (IsLeaf K (f u) ↔ IsLeaf H u) ∧
    (IsOneSplit K (f u) ↔ IsOneSplit H u) ∧
    (IsTwoSplit K (f u) ↔ IsTwoSplit H u) := by
  dsimp [IsLeaf, IsOneSplit, IsTwoSplit] at *
  tauto

/-- A finite meet-preserving copy B -> C composed with a global
diary preembedding C -> K becomes a bounded finite leaf
preembedding B -> K. No convexity of either target image is used. -/
theorem FiniteMeetEmbedding.comp_diaryPreembedding
    {B C K : Ordered3Graph Nat} {k : Nat}
    {h θ : Nat → Nat}
    (DB : FiniteRoleDiaryBlock B k)
    (E : FiniteMeetEmbedding B C k h)
    (P : DiaryPreembeddingSpec C K θ) :
    FiniteLeafPreembedding B K k (θ (h k))
      (fun u => θ (h u)) := by
  let f : Nat → Nat := fun u => θ (h u)
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
  · change θ (h 0) = 0
    rw [E.marker_zero, P.marker_zero]
  · change θ (h 1) = 1
    rw [E.marker_one, P.marker_one]
  · change θ (h 2) = 2
    rw [E.marker_two, P.marker_two]
  · intro u hun
    exact P.strictMono (E.strictMono hun)
  · intro u hu3 hun
    have hValid := DB.prediary.role_valid u hu3 hun
    have hLeaf : IsLeaf B u → IsLeaf K (f u) := by
      intro hu
      exact P.leaf_role (h u) ((E.leaf_iff u hu3 hun).mpr hu)
    have hOne : IsOneSplit B u → IsOneSplit K (f u) := by
      intro hu
      exact P.one_split_role (h u)
        ((E.oneSplit_iff u hu3 hun).mpr hu)
    have hTwo : IsTwoSplit B u → IsTwoSplit K (f u) := by
      intro hu
      exact P.two_split_role (h u)
        ((E.twoSplit_iff u hu3 hun).mpr hu)
    exact finite_role_equiv_of_role_preservation
      f u hValid hLeaf hOne hTwo
  · intro a b c hab hbc hcn ha hb hc
    have han : a < k := by omega
    have hbn : b < k := by omega
    have hCa : IsLeaf C (h a) :=
      (E.leaf_iff a ha.1 han).mpr ha
    have hCb : IsLeaf C (h b) :=
      (E.leaf_iff b hb.1 hbn).mpr hb
    have hCc : IsLeaf C (h c) :=
      (E.leaf_iff c hc.1 hcn).mpr hc
    change K.edge (θ (h a)) (θ (h b)) (θ (h c)) ↔
      B.edge a b c
    exact (P.leaf_edge_iff (h a) (h b) (h c)
      (E.strictMono hab) (E.strictMono hbc)
      hCa hCb hCc).symm.trans (E.edge_iff a b c hab hbc hcn)
  · intro u v hu3 hun hv3 hvn hu hv
    have hCu : IsLeaf C (h u) :=
      (E.leaf_iff u hu3 hun).mpr hu
    have hCv : IsLeaf C (h v) :=
      (E.leaf_iff v hv3 hvn).mpr hv
    change K.oneMeetLevel (θ (h u)) (θ (h v)) =
      θ (h (B.oneMeetLevel u v))
    calc
      K.oneMeetLevel (θ (h u)) (θ (h v)) =
          θ (C.oneMeetLevel (h u) (h v)) :=
        P.leaf_one_meet (h u) (h v) hCu hCv
      _ = θ (h (B.oneMeetLevel u v)) :=
        congrArg θ (E.oneMeet u v hu3 hun hv3 hvn)
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
      ha hb hc hd
    have hCa : IsLeaf C (h a) :=
      (E.leaf_iff a ha3 han).mpr ha
    have hCb : IsLeaf C (h b) :=
      (E.leaf_iff b hb3 hbn).mpr hb
    have hCc : IsLeaf C (h c) :=
      (E.leaf_iff c hc3 hcn).mpr hc
    have hCd : IsLeaf C (h d) :=
      (E.leaf_iff d hd3 hdn).mpr hd
    change K.twoMeetLevel
        (θ (h a)) (θ (h b)) (θ (h c)) (θ (h d)) =
      θ (h (B.twoMeetLevel a b c d))
    calc
      K.twoMeetLevel
          (θ (h a)) (θ (h b)) (θ (h c)) (θ (h d)) =
          θ (C.twoMeetLevel (h a) (h b) (h c) (h d)) :=
        P.leaf_two_meet (h a) (h b) (h c) (h d)
          (E.strictMono hab) (E.strictMono hcd)
          hCa hCb hCc hCd
      _ = θ (h (B.twoMeetLevel a b c d)) :=
        congrArg θ (E.twoMeet a b c d hab hcd
          ha3 han hb3 hbn hc3 hcn hd3 hdn)

/-- For every finite full diary A, every unordered generic
hypergraph embedding into the leaves of a countable full diary
contains an induced copy of A, with its ORIGINAL leaf images
inside the given generic image. All leaf meets and roles survive. -/
theorem exists_finite_diary_in_generic_leaf_range
    {A K : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (G : GenericEnumerated3Graph)
    (F : UnorderedEmbedding G.graph K)
    (DK : RoleDiary K)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t)) :
    ∃ (m : Nat) (g : Nat → Nat),
      FiniteLeafPreembedding A K n m g ∧
      (∀ a b c : Nat, a < b → b < c → c < n →
        (K.edge (g a) (g b) (g c) ↔ A.edge a b c)) ∧
      (∀ u : Nat, 3 ≤ u → u < n → IsLeaf A u →
        ∃ t : Nat, g u = F t) := by
  classical
  obtain ⟨B,k,DB,hAbs⟩ :=
    exists_finiteDiary_universal_flip_absorber DA
  let D : FiniteDiaryInput := ⟨B,k,DB⟩
  obtain ⟨C,DC,hContains⟩ :=
    exists_countableDiary_for_finiteFamily [D]
  obtain ⟨h,E⟩ := hContains D (by simp)
  obtain ⟨θ,P,hRange⟩ :=
    DC.exists_preembedding_into_leaf_range G K F hFleaf DK
  let f : Nat → Nat := fun v => θ (h v)
  let m := θ (h k)
  have PB : FiniteLeafPreembedding B K k m f :=
    E.comp_diaryPreembedding DB P
  obtain ⟨g,Q,hInduced,hLeafSub⟩ :=
    exists_induced_finite_source_in_countable_of_absorber_preembedding
      DA DB DK hAbs PB
  refine ⟨m,g,Q,hInduced,?_⟩
  intro u hu3 hun huLeaf
  obtain ⟨v,hvk,hvLeaf,hgu⟩ :=
    hLeafSub u hu3 hun huLeaf
  have hv3 : 3 ≤ v := hvLeaf.1
  have hCv : IsLeaf C (h v) :=
    (E.leaf_iff v hv3 hvk).mpr hvLeaf
  obtain ⟨t,ht⟩ := hRange (h v) hCv
  refine ⟨t,?_⟩
  calc
    g u = f v := hgu
    _ = θ (h v) := rfl
    _ = F t := ht

end DiaryLeafPriority
end ThreeUniformDiaries
