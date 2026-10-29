import ThreeUniformDiaries.DiaryFiniteCanonicalSignRootedCarrier

/-!
# First real split-bit difference between canonical finite flips

A canonical source flip is identified by a faithful, constrained
finite signature: ONE global Devlin sign and one selected E3 bit
for each genuine source two-split. The code is not a free cube.

Distinct genuine source flips either have different global
signs, or else have a FIRST actual two-split where their
selected witness E3 bits differ. In the second case their
sign-rooted original nodes are LITERALLY equal at that split,
because the node records only S2 bits at STRICTLY earlier cuts.

This supplies the rigorous finite combinatorial choice needed
for the later geometric separation proof. No arbitrary Boolean
signature is assumed to be realised by a diary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any two distinct Boolean functions on a finite linearly
ordered genuine index set have a first differing coordinate. -/
theorem finiteBoolFunction_first_difference
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (σ τ : ι → Bool) (hDiff : σ ≠ τ) :
    ∃ s : ι, σ s ≠ τ s ∧
      (∀ t : ι, t < s → σ t = τ t) := by
  classical
  have hSome : ∃ s : ι, σ s ≠ τ s := by
    by_contra hNone
    apply hDiff
    funext t
    by_cases ht : σ t = τ t
    · exact ht
    · exact False.elim (hNone ⟨t,ht⟩)
  let D : Finset ι := Finset.univ.filter (fun s => σ s ≠ τ s)
  have hD : D.Nonempty := by
    obtain ⟨s,hs⟩ := hSome
    exact ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ s,hs⟩⟩
  let s := D.min' hD
  have hs : σ s ≠ τ s :=
    (Finset.mem_filter.mp (Finset.min'_mem D hD)).2
  refine ⟨s,hs,?_⟩
  intro t hts
  by_contra hBad
  have ht : t ∈ D := Finset.mem_filter.mpr
    ⟨Finset.mem_univ t,hBad⟩
  exact (not_le_of_gt hts) (Finset.min'_le D t ht)

/-- The finite sign-rooted signature is INJECTIVE on the true
canonical source-flip orbit, including the degenerate case with
no ordered source leaf pair. This is not a claim about arbitrary
unrealised Boolean signatures. -/
theorem finiteCanonicalSignRooted_signature_injective
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    Function.Injective
      (fun i : FiniteCanonicalFlipIndex A n =>
        (finiteCanonicalSignRootedFamily DA).signature i) := by
  intro i j hSig
  let F := finiteCanonicalSignRootedFamily DA
  apply Subtype.ext
  apply finiteCanonicalSourceFlipCodes_decode_injective A n
    i.val j.val i.property j.property
  exact finiteUnconditionalFlipSignature_injective_on_flips
    DA (F.flip i) (F.flip j) hSig

/-- Adversarially exact dichotomy: two different ACTUAL canonical
flips have unequal GLOBAL sign, or a first genuine two-split
witness bit difference with all earlier coordinates agreeing.
At that split their nodes in the original sign-rooted causal
carrier are identical. The current split bit itself is NOT
included in the shared node prefix. -/
theorem finiteCanonicalSignRooted_first_difference
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (hij : i ≠ j) :
    (finiteCanonicalSignRootedFamily DA).signature i |>.1 ≠
      (finiteCanonicalSignRootedFamily DA).signature j |>.1 ∨
    (∃ s : FiniteTwoSplitIndex A n,
      ((finiteCanonicalSignRootedFamily DA).signature i).1 =
        ((finiteCanonicalSignRootedFamily DA).signature j).1 ∧
      ((finiteCanonicalSignRootedFamily DA).signature i).2 s ≠
        ((finiteCanonicalSignRootedFamily DA).signature j).2 s ∧
      (∀ t : FiniteTwoSplitIndex A n, t.val.val < s.val.val →
        ((finiteCanonicalSignRootedFamily DA).signature i).2 t =
          ((finiteCanonicalSignRootedFamily DA).signature j).2 t) ∧
      (finiteCanonicalSignRootedFamily DA).node i s.val.val =
        (finiteCanonicalSignRootedFamily DA).node j s.val.val) := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  by_cases hSign : (F.signature i).1 = (F.signature j).1
  · right
    have hOther : (F.signature i).2 ≠ (F.signature j).2 := by
      intro hS2
      apply hij
      exact finiteCanonicalSignRooted_signature_injective DA
        (Prod.ext hSign hS2)
    obtain ⟨s,hdiff,hBefore⟩ :=
      finiteBoolFunction_first_difference
        (F.signature i).2 (F.signature j).2 hOther
    have hPrefix :
        ∀ t : FiniteTwoSplitIndex A n,
          t.val.val < s.val.val →
          (F.signature i).2 t = (F.signature j).2 t := by
      intro t hts
      exact hBefore t hts
    have hs3 : 3 ≤ s.val.val := s.property.1
    have hShared : F.node i s.val.val = F.node j s.val.val := by
      apply Prod.ext
      · rfl
      · have hNot : ¬ s.val.val < 3 := by omega
        simp only [FiniteSignRootedFlipFamily.node,if_neg hNot]
        apply congrArg some
        apply Prod.ext
        · exact hSign
        · funext t
          by_cases hlt : t.val.val < s.val.val
          · simp only [if_pos hlt,hPrefix t hlt]
          · simp only [if_neg hlt]
    exact ⟨s,hSign,hdiff,hPrefix,hShared⟩
  · exact Or.inl hSign

end DiaryLeafPriority
end ThreeUniformDiaries
