import ThreeUniformDiaries.FiniteInfiniteAuxCanonicalCoherence
import ThreeUniformDiaries.FiniteCoupledCanonicalMaps
import ThreeUniformDiaries.InfiniteCanonicalSuccessor

/-!
# Coherence of the finite and infinite genuine E1 canonical recursions

For a synchronized genuine infinite one/aux pair of strong pictures,
restrict both pictures to the first k+1 selected levels.
Their finite singleton canonical map agrees literally with the
infinite singleton canonical map on every source OneNode i (i<=k).
The successor parameter is the corresponding E2 image, whose
finite/infinite coherence is proved first.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finitePrefix_oneCanonicalMap_eq_infinite
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (k : Nat) :
    ∀ (i : Nat) (hi : i ≤ k) (a : OneNode i),
      (finiteStrongPicture_oneCanonicalMap
        (infiniteStrongPicture_finitePrefix_strong h₁ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₂ hf rfl k)
        i hi a).val =
        (infiniteOneCanonicalMap h₁ h₂ i a).val := by
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
      let prevF := finiteStrongPicture_oneCanonicalMap
        hF₁ hF₂ i hi0 (a.truncate i)
      let prevI := infiniteOneCanonicalMap h₁ h₂ i (a.truncate i)
      let c : AuxNode i := a.boundaryAux i
      let paramF := finiteStrongPicture_auxCanonicalMap hF₂ i hi0 c
      let paramI := infiniteAuxCanonicalMap h₂ i c
      let curF := finiteStrongPicture_oneCanonicalMap
        hF₁ hF₂ (i + 1) hi a
      let curI := infiniteOneCanonicalMap h₁ h₂ (i + 1) a
      have hprev : prevF.val = prevI.val := ih hi0 (a.truncate i)
      have hparam : paramF.val = paramI.val :=
        finitePrefix_auxCanonicalMap_eq_infinite
          h₂ hf rfl k i hi0 c
      have hfiniteCone0 :
          CoordNode.one (f i + 1)
              (prevF.val.succ paramF.val) ≤
            CoordNode.one (f (i + 1)) curF.val := by
        change CoordNode.one (f i + 1)
          (prevF.val.succ paramF.val) ≤
            CoordNode.one (f (i + 1))
              (finiteStrongPicture_oneStep hF₁ i hik
                prevF.val prevF.property paramF.val)
        exact (finiteStrongPicture_oneStep_spec hF₁ i hik
          prevF.val prevF.property paramF.val).2
      have hfiniteCone :
          CoordNode.one (f i + 1)
              (prevI.val.succ paramI.val) ≤
            CoordNode.one (f (i + 1)) curF.val := by
        simpa only [hprev, hparam] using hfiniteCone0
      have hinfiniteCone :
          CoordNode.one (f i + 1)
              (prevI.val.succ paramI.val) ≤
            CoordNode.one (f (i + 1)) curI.val := by
        have hcone := infiniteOneCanonicalMap_succ
          h₁ h₂ i (a.truncate i) c
        rw [OneNode.succ_truncate_boundary] at hcone
        exact hcone
      obtain ⟨b, _, hunique⟩ :=
        infiniteStrongPicture_one_lift h₁ i
          prevI.val prevI.property paramI.val
      have hfin : curF.val = b :=
        hunique curF.val ⟨curF.property.1, hfiniteCone⟩
      have hinf : curI.val = b :=
        hunique curI.val ⟨curI.property, hinfiniteCone⟩
      exact hfin.trans hinf.symm

end CoordNode
end ThreeUniformDiaries
