import ThreeUniformDiaries.InfiniteOneFirstDisagreement
import ThreeUniformDiaries.InfiniteCanonicalAuxOneRestriction
import ThreeUniformDiaries.CoordinateTree

/-!
# Full meet preservation of genuine infinite singleton canonical maps

For arbitrary source singleton nodes, possibly at different levels,
their common-prefix meet is preserved by the actual infinite
geometric canonical map, even when the selected target levels skip
arbitrarily many ambient indices.

Comparable source nodes are handled by the checked restriction
identity. Incomparable nodes have a first differing auxiliary bit;
the previously checked geometric first-disagreement lemma gives
their precise image meet. This supplies full meet preservation,
hence meet closure of images, in the singleton coordinate of the
canonical-composition lemma.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteOneCanonicalMap_preserves_meet
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {N M : Nat} (u : OneNode N) (v : OneNode M) :
    let n := meetLevel (.one N u) (.one M v)
    meet
      (.one (f N) (infiniteOneCanonicalMap h₁ h₂ N u).val)
      (.one (f M) (infiniteOneCanonicalMap h₁ h₂ M v).val) =
      .one (f n)
        (infiniteOneCanonicalMap h₁ h₂ n (u.truncate n)).val := by
  classical
  dsimp only
  let X : CoordNode := .one N u
  let Y : CoordNode := .one M v
  let n := meetLevel X Y
  let U : CoordNode := .one (f N) (infiniteOneCanonicalMap h₁ h₂ N u).val
  let V : CoordNode := .one (f M) (infiniteOneCanonicalMap h₁ h₂ M v).val
  have hzero : u.truncate 0 = v.truncate 0 := by
    apply OneNode.ext_pairs
    funext i j
    rw [(u.truncate 0).support i j (by omega),
        (v.truncate 0).support i j (by omega)]
  have hrootX : CoordNode.one 0 (u.truncate 0) ≤ X := by
    refine ⟨Nat.zero_le _, ?_⟩
    rfl
  have hrootY : CoordNode.one 0 (u.truncate 0) ≤ Y := by
    refine ⟨Nat.zero_le _, ?_⟩
    change CoordNode.one 0 (v.truncate 0) =
      CoordNode.one 0 (u.truncate 0)
    exact congrArg (fun a : OneNode 0 => CoordNode.one 0 a) hzero.symm
  have hcommon : ∃ p : CoordNode, p ≤ X ∧ p ≤ Y :=
    ⟨.one 0 (u.truncate 0), hrootX, hrootY⟩
  have hsrcCut : u.truncate n = v.truncate n := by
    have h := meetLevel_spec (a := X) (b := Y) hcommon
    change CoordNode.one n (u.truncate n) =
      CoordNode.one n (v.truncate n) at h
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
        change CoordNode.one (n + 1) (u.truncate (n + 1)) =
          CoordNode.one (n + 1) (v.truncate (n + 1))
        rw [heq]
      have hbound : n + 1 ≤ min (level X) (level Y) := by
        simp only [X, Y, level]
        omega
      have hlarge : n + 1 ≤ meetLevel X Y :=
        Nat.le_findGreatest hbound hprop
      change n + 1 ≤ n at hlarge
      omega
    have hsA :
        (u.truncate n).succ (u.boundaryAux n) = u.truncate (n + 1) := by
      have h := (u.truncate (n + 1)).succ_truncate_boundary
      rw [u.truncate_truncate (Nat.le_succ n)] at h
      have hb : (u.truncate (n + 1)).boundaryAux n = u.boundaryAux n := by
        exact OneNode.boundaryAux_truncate_next _ _
      rw [hb] at h
      exact h
    have hsB :
        (v.truncate n).succ (v.boundaryAux n) = v.truncate (n + 1) := by
      have h := (v.truncate (n + 1)).succ_truncate_boundary
      rw [v.truncate_truncate (Nat.le_succ n)] at h
      have hb : (v.truncate (n + 1)).boundaryAux n = v.boundaryAux n := by
        exact OneNode.boundaryAux_truncate_next _ _
      rw [hb] at h
      exact h
    have hdiff : u.boundaryAux n ≠ v.boundaryAux n := by
      intro hb
      have heq : u.truncate (n + 1) = v.truncate (n + 1) := by
        calc
          u.truncate (n + 1) =
              (u.truncate n).succ (u.boundaryAux n) := hsA.symm
          _ = (v.truncate n).succ (v.boundaryAux n) := by
              rw [hsrcCut, hb]
          _ = v.truncate (n + 1) := hsB
      exact hnextDiff heq
    change meet U V =
      CoordNode.one (f n)
        (infiniteOneCanonicalMap h₁ h₂ n (u.truncate n)).val
    exact infiniteOneCanonicalMap_firstDisagreement_meet
      h₁ h₂ hf u v hnltN hnltM hsrcCut hdiff
  · by_cases hNM : N ≤ M
    · have hn : n = N := by omega
      have hsrc : u = v.truncate N := by
        rw [hn] at hsrcCut
        simpa using hsrcCut
      have htr := infiniteOneCanonicalMap_truncate h₁ h₂ hf
        N M hNM v
      have hUV : U ≤ V := by
        refine ⟨hf.monotone hNM, ?_⟩
        change
          CoordNode.one (f N)
            ((infiniteOneCanonicalMap h₁ h₂ M v).val.truncate (f N)) =
          CoordNode.one (f N) (infiniteOneCanonicalMap h₁ h₂ N u).val
        rw [htr, ← hsrc]
      have hmeet : meet U V = U := by
        have hc : ∃ p : CoordNode, p ≤ U ∧ p ≤ V :=
          ⟨U, le_refl U, hUV⟩
        exact le_antisymm (meet_le_left hc)
          (le_meet (le_refl U) hUV)
      change meet U V =
        CoordNode.one (f n)
          (infiniteOneCanonicalMap h₁ h₂ n (u.truncate n)).val
      rw [hn]
      simpa [U] using hmeet
    · have hMN : M ≤ N := by omega
      have hn : n = M := by omega
      have hsrc : v = u.truncate M := by
        rw [hn] at hsrcCut
        simpa using hsrcCut.symm
      have htr := infiniteOneCanonicalMap_truncate h₁ h₂ hf
        M N hMN u
      have hVU : V ≤ U := by
        refine ⟨hf.monotone hMN, ?_⟩
        change
          CoordNode.one (f M)
            ((infiniteOneCanonicalMap h₁ h₂ N u).val.truncate (f M)) =
          CoordNode.one (f M) (infiniteOneCanonicalMap h₁ h₂ M v).val
        rw [htr, ← hsrc]
      have hmeet : meet U V = V := by
        have hc : ∃ p : CoordNode, p ≤ U ∧ p ≤ V :=
          ⟨V, hVU, le_refl V⟩
        exact le_antisymm (meet_le_right hc)
          (le_meet hVU (le_refl V))
      change meet U V =
        CoordNode.one (f n)
          (infiniteOneCanonicalMap h₁ h₂ n (u.truncate n)).val
      rw [hn]
      simpa [V, hsrc] using hmeet

end CoordNode
end ThreeUniformDiaries
