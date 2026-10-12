import ThreeUniformDiaries.FiniteInfiniteOneCanonicalCoherence
import ThreeUniformDiaries.FiniteCoupledCanonicalMaps
import ThreeUniformDiaries.InfiniteCanonicalSuccessor

/-!
# Coherence of the finite and infinite genuine E0 canonical recursions

For a synchronized genuine infinite enumeration/one/aux triple of
strong pictures, restrict all coordinates to the first k+1
selected levels. At every source EnumNode i with i<=k, the actual
finite E0 canonical map equals the restriction of the independent
infinite E0 recursion.

The successor parameter is an E1 image, already identified by the
finite/infinite E1 theorem, which in turn uses the E2 theorem.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finitePrefix_enumCanonicalMap_eq_infinite
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (k : Nat) :
    ∀ (i : Nat) (hi : i ≤ k) (a : EnumNode i),
      (finiteStrongPicture_enumCanonicalMap
        (infiniteStrongPicture_finitePrefix_strong h₀ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₁ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₂ hf rfl k)
        i hi a).val =
        (infiniteEnumCanonicalMap h₀ h₁ h₂ i a).val := by
  let hF₀ := infiniteStrongPicture_finitePrefix_strong h₀ hf rfl k
  let hF₁ := infiniteStrongPicture_finitePrefix_strong h₁ hf rfl k
  let hF₂ := infiniteStrongPicture_finitePrefix_strong h₂ hf rfl k
  intro i
  induction i with
  | zero =>
      intro hi a
      rfl
  | succ i ih =>
      intro hi a
      have hik : i < k := by omega
      have hi0 : i ≤ k := Nat.le_of_lt hik
      let prevF := finiteStrongPicture_enumCanonicalMap
        hF₀ hF₁ hF₂ i hi0 (a.truncate i)
      let prevI := infiniteEnumCanonicalMap h₀ h₁ h₂ i (a.truncate i)
      let b : OneNode i := a.boundaryOne i
      let paramF := finiteStrongPicture_oneCanonicalMap hF₁ hF₂ i hi0 b
      let paramI := infiniteOneCanonicalMap h₁ h₂ i b
      let curF := finiteStrongPicture_enumCanonicalMap
        hF₀ hF₁ hF₂ (i + 1) hi a
      let curI := infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1) a
      have hprev : prevF.val = prevI.val := ih hi0 (a.truncate i)
      have hparam : paramF.val = paramI.val :=
        finitePrefix_oneCanonicalMap_eq_infinite
          h₁ h₂ hf k i hi0 b
      have hfiniteCone0 :
          CoordNode.enum (f i + 1)
              (prevF.val.succ paramF.val) ≤
            CoordNode.enum (f (i + 1)) curF.val := by
        change CoordNode.enum (f i + 1)
          (prevF.val.succ paramF.val) ≤
            CoordNode.enum (f (i + 1))
              (finiteStrongPicture_enumStep hF₀ i hik
                prevF.val prevF.property paramF.val)
        exact (finiteStrongPicture_enumStep_spec hF₀ i hik
          prevF.val prevF.property paramF.val).2
      have hfiniteCone :
          CoordNode.enum (f i + 1)
              (prevI.val.succ paramI.val) ≤
            CoordNode.enum (f (i + 1)) curF.val := by
        simpa only [hprev, hparam] using hfiniteCone0
      have hinfiniteCone :
          CoordNode.enum (f i + 1)
              (prevI.val.succ paramI.val) ≤
            CoordNode.enum (f (i + 1)) curI.val := by
        have hcone := infiniteEnumCanonicalMap_succ
          h₀ h₁ h₂ i (a.truncate i) b
        rw [EnumNode.succ_truncate_boundary] at hcone
        exact hcone
      obtain ⟨c, _, hunique⟩ :=
        infiniteStrongPicture_enum_lift h₀ i
          prevI.val prevI.property paramI.val
      have hfin : curF.val = c :=
        hunique curF.val ⟨curF.property.1, hfiniteCone⟩
      have hinf : curI.val = c :=
        hunique curI.val ⟨curI.property, hinfiniteCone⟩
      exact hfin.trans hinf.symm

end CoordNode
end ThreeUniformDiaries
