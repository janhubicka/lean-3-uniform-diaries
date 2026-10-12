import ThreeUniformDiaries.InfiniteToFiniteStrongPrefix
import ThreeUniformDiaries.FiniteAuxCanonicalMap
import ThreeUniformDiaries.InfiniteCanonicalSuccessor

/-!
# Coherence of finite and infinite genuine E2 canonical recursions

Take the finite strong prefix of height k+1 of any actual infinite
auxiliary coordinate strong picture. The *finite* canonical map
defined by the selected-child recursion agrees literally, on
every source AuxNode i with i<=k, with the restriction of the
independently defined *infinite* canonical map.

The argument uses the unique lifted Boolean successor in the
infinite strong tree. It does NOT postulate agreement as an
additional field of CanonicalMap or of the finite strong picture.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finitePrefix_auxCanonicalMap_eq_infinite
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (hf : StrictMono f) (hr : level (.aux (f 0) r) = f 0)
    (k : Nat) :
    ∀ (i : Nat) (hi : i ≤ k) (a : AuxNode i),
      (finiteStrongPicture_auxCanonicalMap
        (infiniteStrongPicture_finitePrefix_strong hS hf hr k)
        i hi a).val =
        (infiniteAuxCanonicalMap hS i a).val := by
  let hF := infiniteStrongPicture_finitePrefix_strong hS hf hr k
  intro i
  induction i with
  | zero =>
      intro hi a
      rfl
  | succ i ih =>
      intro hi a
      have hik : i < k := by omega
      have hi0 : i ≤ k := Nat.le_of_lt hik
      let prevF := finiteStrongPicture_auxCanonicalMap
        hF i hi0 (a.truncate i)
      let prevI := infiniteAuxCanonicalMap hS i (a.truncate i)
      let curF := finiteStrongPicture_auxCanonicalMap
        hF (i + 1) hi a
      let curI := infiniteAuxCanonicalMap hS (i + 1) a
      have hprev : prevF.val = prevI.val :=
        ih hi0 (a.truncate i)
      have hfiniteCone0 :
          CoordNode.aux (f i + 1) (prevF.val.succ (a.bit i)) ≤
            CoordNode.aux (f (i + 1)) curF.val := by
        change CoordNode.aux (f i + 1)
          (prevF.val.succ (a.bit i)) ≤
            CoordNode.aux (f (i + 1))
              (finiteStrongPicture_auxStep hF i hik
                prevF.val prevF.property (a.bit i))
        exact (finiteStrongPicture_auxStep_spec hF i hik
          prevF.val prevF.property (a.bit i)).2
      have hfiniteCone :
          CoordNode.aux (f i + 1) (prevI.val.succ (a.bit i)) ≤
            CoordNode.aux (f (i + 1)) curF.val := by
        simpa only [hprev] using hfiniteCone0
      have hinfiniteCone :
          CoordNode.aux (f i + 1) (prevI.val.succ (a.bit i)) ≤
            CoordNode.aux (f (i + 1)) curI.val := by
        have hcone :=
          infiniteAuxCanonicalMap_succ hS i
            (a.truncate i) (a.bit i)
        rw [AuxNode.succ_truncate_new] at hcone
        exact hcone
      obtain ⟨b, _, hunique⟩ :=
        infiniteStrongPicture_aux_lift hS i
          prevI.val prevI.property (a.bit i)
      have hfin : curF.val = b :=
        hunique curF.val ⟨curF.property.1, hfiniteCone⟩
      have hinf : curI.val = b :=
        hunique curI.val ⟨curI.property, hinfiniteCone⟩
      exact hfin.trans hinf.symm

end CoordNode
end ThreeUniformDiaries
