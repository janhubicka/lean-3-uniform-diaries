import ThreeUniformDiaries.SizeFirstNumericCode
import Mathlib.Order.OrderIsoNat

/-!
# Length-first enumeration of the relative universal branch hypergraph

The numeric coding module maps K_I injectively into the naturals,
with all shorter nodes preceding longer ones. Its range is infinite,
since a canonical node exists at every finite length. Mathlib's
order isomorphism Nat.Subtype.orderIsoOfNat enumerates the occupied
codes increasingly. Inverting the code then yields an actual
bijection Nat ≃ K_I, ordered by nondecreasing finite length.

This is the enumeration required by the repaired Lemma Kiemb.
The subsequent parent schedule and exact branch meets are separate.
-/

namespace ThreeUniformDiaries

/-- The occupied integer codes form an infinite set, witnessed by
the canonical zero-extension branch through all levels. -/
theorem relativeBranchCodeRange_infinite
    {n : Nat} (I : EnumNode n) :
    Infinite {v : Nat // v ∈ Set.range (relativeBranchNumericCode I)} := by
  let f : Nat → {v : Nat // v ∈ Set.range (relativeBranchNumericCode I)} :=
    fun k => ⟨relativeBranchNumericCode I (relativeBranchCanonical I k),
      ⟨relativeBranchCanonical I k, rfl⟩⟩
  have hf : Function.Injective f := by
    intro k l h
    have hcode : relativeBranchNumericCode I (relativeBranchCanonical I k) =
        relativeBranchNumericCode I (relativeBranchCanonical I l) :=
      congrArg Subtype.val h
    have hnodes := relativeBranchNumericCode_injective I hcode
    have hlast := congrArg (fun A : RelativeBranchNode I => A.val.last) hnodes
    simpa using hlast
  exact Infinite.of_injective f hf

/-- An equivalence of K_I with its numerical code range. -/
noncomputable def relativeBranchCodeEquivRange
    {n : Nat} (I : EnumNode n) :
    RelativeBranchNode I ≃
      {v : Nat // v ∈ Set.range (relativeBranchNumericCode I)} := by
  classical
  let f : RelativeBranchNode I →
      {v : Nat // v ∈ Set.range (relativeBranchNumericCode I)} :=
    fun A => ⟨relativeBranchNumericCode I A, ⟨A, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro A B h
    exact relativeBranchNumericCode_injective I (congrArg Subtype.val h)
  · intro x
    rcases x.property with ⟨A, hA⟩
    refine ⟨A, ?_⟩
    apply Subtype.ext
    exact hA

/-- Increasingly enumerate the occupied numerical codes. -/
noncomputable def relativeBranchRangeOrderIso
    {n : Nat} (I : EnumNode n) :
    Nat ≃o {v : Nat // v ∈ Set.range (relativeBranchNumericCode I)} := by
  letI : Infinite {v : Nat // v ∈ Set.range (relativeBranchNumericCode I)} :=
    relativeBranchCodeRange_infinite I
  exact Nat.Subtype.orderIsoOfNat (Set.range (relativeBranchNumericCode I))

/-- The desired size-first enumeration of all vertices of relative K_I. -/
noncomputable def relativeBranchSizeFirstEquiv
    {n : Nat} (I : EnumNode n) : Nat ≃ RelativeBranchNode I :=
  (relativeBranchRangeOrderIso I).toEquiv.trans
    (relativeBranchCodeEquivRange I).symm

/-- The numeric code of the k-th node is the k-th occupied integer. -/
theorem relativeBranchSizeFirst_code
    {n : Nat} (I : EnumNode n) (k : Nat) :
    relativeBranchNumericCode I (relativeBranchSizeFirstEquiv I k) =
      ((relativeBranchRangeOrderIso I) k).val := by
  change relativeBranchNumericCode I
      ((relativeBranchCodeEquivRange I).symm
        ((relativeBranchRangeOrderIso I) k)) =
      ((relativeBranchRangeOrderIso I) k).val
  have h := (relativeBranchCodeEquivRange I).apply_symm_apply
    ((relativeBranchRangeOrderIso I) k)
  exact congrArg Subtype.val h

/-- The actual enumeration is nondecreasing by the number of vertices. -/
theorem relativeBranchSizeFirst_length_mono
    {n : Nat} (I : EnumNode n) :
    Monotone (fun k : Nat => (relativeBranchSizeFirstEquiv I k).val.last) := by
  intro k l hkl
  by_contra hbad
  have hreverse : (relativeBranchSizeFirstEquiv I l).val.last <
      (relativeBranchSizeFirstEquiv I k).val.last := by
    exact Nat.lt_of_not_ge hbad
  have hreverseCode := relativeBranchNumericCode_lt_of_last_lt I hreverse
  have hforwardCode :
      relativeBranchNumericCode I (relativeBranchSizeFirstEquiv I k) ≤
        relativeBranchNumericCode I (relativeBranchSizeFirstEquiv I l) := by
    rw [relativeBranchSizeFirst_code I k,
      relativeBranchSizeFirst_code I l]
    exact (relativeBranchRangeOrderIso I).monotone hkl
  omega

end ThreeUniformDiaries
