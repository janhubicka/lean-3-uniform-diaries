import ThreeUniformDiaries.InfiniteAuxFirstDisagreement
import ThreeUniformDiaries.InfiniteCanonicalAuxOneRestriction
import ThreeUniformDiaries.CoordinateTree

/-!
# Full meet preservation of genuine infinite auxiliary canonical maps

For arbitrary source auxiliary nodes, possibly at different levels,
their common-prefix meet is preserved by the actual infinite
geometric canonical map, even when the selected target levels skip
arbitrarily many ambient indices.

Comparable source nodes are handled by the checked restriction
identity. Incomparable nodes have a first differing auxiliary bit;
the previously checked geometric first-disagreement lemma gives
their precise image meet. This supplies full meet preservation,
hence meet closure of images, in the auxiliary coordinate of the
canonical-composition lemma.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteAuxCanonicalMap_preserves_meet
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (hf : StrictMono f)
    {N M : Nat} (u : AuxNode N) (v : AuxNode M) :
    let n := meetLevel (.aux N u) (.aux M v)
    meet
      (.aux (f N) (infiniteAuxCanonicalMap hS N u).val)
      (.aux (f M) (infiniteAuxCanonicalMap hS M v).val) =
      .aux (f n)
        (infiniteAuxCanonicalMap hS n (u.truncate n)).val := by
  classical
  dsimp only
  let X : CoordNode := .aux N u
  let Y : CoordNode := .aux M v
  let n := meetLevel X Y
  let U : CoordNode := .aux (f N) (infiniteAuxCanonicalMap hS N u).val
  let V : CoordNode := .aux (f M) (infiniteAuxCanonicalMap hS M v).val
  have hzero : u.truncate 0 = v.truncate 0 := by
    apply AuxNode.ext_bits
    funext k
    rw [(u.truncate 0).support k (Nat.zero_le k),
        (v.truncate 0).support k (Nat.zero_le k)]
  have hrootX : CoordNode.aux 0 (u.truncate 0) ≤ X := by
    refine ⟨Nat.zero_le _, ?_⟩
    rfl
  have hrootY : CoordNode.aux 0 (u.truncate 0) ≤ Y := by
    refine ⟨Nat.zero_le _, ?_⟩
    change CoordNode.aux 0 (v.truncate 0) =
      CoordNode.aux 0 (u.truncate 0)
    exact congrArg (fun a : AuxNode 0 => CoordNode.aux 0 a) hzero.symm
  have hcommon : ∃ p : CoordNode, p ≤ X ∧ p ≤ Y :=
    ⟨.aux 0 (u.truncate 0), hrootX, hrootY⟩
  have hsrcCut : u.truncate n = v.truncate n := by
    have h := meetLevel_spec (a := X) (b := Y) hcommon
    change CoordNode.aux n (u.truncate n) =
      CoordNode.aux n (v.truncate n) at h
    injection h
  have hnN : n ≤ N := by
    have h := meetLevel_le_left X Y
    change n ≤ N at h
    exact h
  have hnM : n ≤ M := by
    have h := meetLevel_le_right X Y
    change n ≤ M at h
    exact h
  by_cases hboth : n < N ∧ n < M
  · have hnltN : n < N := hboth.1
    have hnltM : n < M := hboth.2
    have hnextDiff : u.truncate (n + 1) ≠ v.truncate (n + 1) := by
      intro heq
      have hprop : CommonAt X Y (n + 1) := by
        change CoordNode.aux (n + 1) (u.truncate (n + 1)) =
          CoordNode.aux (n + 1) (v.truncate (n + 1))
        rw [heq]
      have hbound : n + 1 ≤ min (level X) (level Y) := by
        simp only [X, Y, level]
        omega
      have hlarge : n + 1 ≤ meetLevel X Y :=
        Nat.le_findGreatest hbound hprop
      change n + 1 ≤ n at hlarge
      omega
    have hsA :
        (u.truncate n).succ (u.bit n) = u.truncate (n + 1) := by
      have h := (u.truncate (n + 1)).succ_truncate_new
      rw [u.truncate_truncate (Nat.le_succ n)] at h
      have hb : (u.truncate (n + 1)).bit n = u.bit n := by
        simp [AuxNode.truncate, Nat.lt_succ_self]
      rw [hb] at h
      exact h
    have hsB :
        (v.truncate n).succ (v.bit n) = v.truncate (n + 1) := by
      have h := (v.truncate (n + 1)).succ_truncate_new
      rw [v.truncate_truncate (Nat.le_succ n)] at h
      have hb : (v.truncate (n + 1)).bit n = v.bit n := by
        simp [AuxNode.truncate, Nat.lt_succ_self]
      rw [hb] at h
      exact h
    have hdiff : u.bit n ≠ v.bit n := by
      intro hb
      have heq : u.truncate (n + 1) = v.truncate (n + 1) := by
        calc
          u.truncate (n + 1) =
              (u.truncate n).succ (u.bit n) := hsA.symm
          _ = (v.truncate n).succ (v.bit n) := by
              rw [hsrcCut, hb]
          _ = v.truncate (n + 1) := hsB
      exact hnextDiff heq
    change meet U V =
      CoordNode.aux (f n)
        (infiniteAuxCanonicalMap hS n (u.truncate n)).val
    exact infiniteAuxCanonicalMap_firstDisagreement_meet
      hS hf u v hnltN hnltM hsrcCut hdiff
  · by_cases hNM : N ≤ M
    · have hn : n = N := by omega
      have hsrc : u = v.truncate N := by
        rw [hn] at hsrcCut
        simpa using hsrcCut
      have htr := infiniteAuxCanonicalMap_truncate hS hf
        N M hNM v
      have hUV : U ≤ V := by
        refine ⟨hf.monotone hNM, ?_⟩
        change
          CoordNode.aux (f N)
            ((infiniteAuxCanonicalMap hS M v).val.truncate (f N)) =
          CoordNode.aux (f N) (infiniteAuxCanonicalMap hS N u).val
        rw [htr, ← hsrc]
      have hmeet : meet U V = U := by
        have hc : ∃ p : CoordNode, p ≤ U ∧ p ≤ V :=
          ⟨U, le_refl U, hUV⟩
        exact le_antisymm (meet_le_left hc)
          (le_meet (le_refl U) hUV)
      change meet U V =
        CoordNode.aux (f n)
          (infiniteAuxCanonicalMap hS n (u.truncate n)).val
      rw [hn]
      simpa [U] using hmeet
    · have hMN : M ≤ N := by omega
      have hn : n = M := by omega
      have hsrc : v = u.truncate M := by
        rw [hn] at hsrcCut
        simpa using hsrcCut.symm
      have htr := infiniteAuxCanonicalMap_truncate hS hf
        M N hMN u
      have hVU : V ≤ U := by
        refine ⟨hf.monotone hMN, ?_⟩
        change
          CoordNode.aux (f M)
            ((infiniteAuxCanonicalMap hS N u).val.truncate (f M)) =
          CoordNode.aux (f M) (infiniteAuxCanonicalMap hS M v).val
        rw [htr, ← hsrc]
      have hmeet : meet U V = V := by
        have hc : ∃ p : CoordNode, p ≤ U ∧ p ≤ V :=
          ⟨V, hVU, le_refl V⟩
        exact le_antisymm (meet_le_right hc)
          (le_meet hVU (le_refl V))
      change meet U V =
        CoordNode.aux (f n)
          (infiniteAuxCanonicalMap hS n (u.truncate n)).val
      rw [hn]
      simpa [V, hsrc] using hmeet

end CoordNode
end ThreeUniformDiaries
