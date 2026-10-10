import ThreeUniformDiaries.InfiniteCanonicalEnumRestriction

/-!
# Selected-level restriction coherence for E2 and E1 infinite maps

Complements the already checked E0 infinite canonical restriction
theorem. For the actual recursively constructed auxiliary and
singleton canonical maps, mapping a source initial segment commutes
with truncation at the corresponding selected target level.

Together, all three coordinate maps preserve the tree ancestor
relation, independently of any abstract CanonicalMap fields. These
geometric facts are prerequisites for the meet-preservation proof
needed by infinite canonical-map composition.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- For the constructed infinite aux map, taking the selected
target ancestor at f(j) recovers the source predecessor's image. -/
theorem infiniteAuxCanonicalMap_parent
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (j : Nat) (a : AuxNode (j + 1)) :
    (infiniteAuxCanonicalMap hS (j + 1) a).val.truncate (f j) =
      (infiniteAuxCanonicalMap hS j (a.truncate j)).val := by
  let p := infiniteAuxCanonicalMap hS j (a.truncate j)
  have hcone := infiniteAuxCanonicalMap_succ hS j (a.truncate j) (a.bit j)
  rw [AuxNode.succ_truncate_new] at hcone
  have hparent :
      CoordNode.aux (f j) p.val ≤
        CoordNode.aux (f j + 1) (p.val.succ (a.bit j)) := by
    refine ⟨Nat.le_succ _, ?_⟩
    change CoordNode.aux (f j)
      ((p.val.succ (a.bit j)).truncate (f j)) =
        CoordNode.aux (f j) p.val
    rw [AuxNode.truncate_succ]
  have htree :
      CoordNode.aux (f j) p.val ≤
        CoordNode.aux (f (j + 1))
          (infiniteAuxCanonicalMap hS (j + 1) a).val :=
    CoordNode.le_trans hparent hcone
  have heq := htree.2
  change CoordNode.aux (f j)
      ((infiniteAuxCanonicalMap hS (j + 1) a).val.truncate (f j)) =
    CoordNode.aux (f j) p.val at heq
  injection heq with hb

/-- Coherence of the actual infinite aux map at every earlier
selected level, including arbitrary skipped ambient levels. -/
theorem infiniteAuxCanonicalMap_truncate
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (hf : StrictMono f)
    (i j : Nat) (hij : i ≤ j) (a : AuxNode j) :
    (infiniteAuxCanonicalMap hS j a).val.truncate (f i) =
      (infiniteAuxCanonicalMap hS i (a.truncate i)).val := by
  have hmain :
      ∀ (j : Nat) (i : Nat) (hij : i ≤ j) (a : AuxNode j),
      (infiniteAuxCanonicalMap hS j a).val.truncate (f i) =
        (infiniteAuxCanonicalMap hS i (a.truncate i)).val := by
    intro j
    induction j with
    | zero =>
        intro i hij a
        have hi : i = 0 := by omega
        subst i
        simp only [AuxNode.truncate_self]
    | succ j ih =>
        intro i hij a
        by_cases heq : i = j + 1
        · subst i
          simp only [AuxNode.truncate_self]
        · have hij0 : i ≤ j := by omega
          have hparent :=
            infiniteAuxCanonicalMap_parent hS j a
          have hprev := ih i hij0 (a.truncate j)
          have hlevels : f i ≤ f j := hf.monotone hij0
          calc
            (infiniteAuxCanonicalMap hS (j + 1) a).val.truncate (f i) =
              ((infiniteAuxCanonicalMap hS (j + 1) a).val.truncate
                (f j)).truncate (f i) := by
                  symm
                  exact AuxNode.truncate_truncate _ hlevels
            _ = (infiniteAuxCanonicalMap hS j (a.truncate j)).val.truncate
                  (f i) := by
                    rw [hparent]
            _ = (infiniteAuxCanonicalMap hS i ((a.truncate j).truncate i)).val :=
              hprev
            _ = (infiniteAuxCanonicalMap hS i (a.truncate i)).val := by
                rw [a.truncate_truncate hij0]
  exact hmain j i hij a


/-- For the constructed infinite one map, taking the selected
target ancestor at f(j) recovers the source predecessor's image. -/
theorem infiniteOneCanonicalMap_parent
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (j : Nat) (a : OneNode (j + 1)) :
    (infiniteOneCanonicalMap h₁ h₂ (j + 1) a).val.truncate (f j) =
      (infiniteOneCanonicalMap h₁ h₂ j (a.truncate j)).val := by
  let p := infiniteOneCanonicalMap h₁ h₂ j (a.truncate j)
  let c := infiniteAuxCanonicalMap h₂ j (a.boundaryAux j)
  have hcone := infiniteOneCanonicalMap_succ h₁ h₂ j (a.truncate j) (a.boundaryAux j)
  rw [OneNode.succ_truncate_boundary] at hcone
  have hparent :
      CoordNode.one (f j) p.val ≤
        CoordNode.one (f j + 1) (p.val.succ c.val) := by
    refine ⟨Nat.le_succ _, ?_⟩
    change CoordNode.one (f j)
      ((p.val.succ c.val).truncate (f j)) =
        CoordNode.one (f j) p.val
    rw [OneNode.truncate_succ]
  have htree :
      CoordNode.one (f j) p.val ≤
        CoordNode.one (f (j + 1))
          (infiniteOneCanonicalMap h₁ h₂ (j + 1) a).val :=
    CoordNode.le_trans hparent hcone
  have heq := htree.2
  change CoordNode.one (f j)
      ((infiniteOneCanonicalMap h₁ h₂ (j + 1) a).val.truncate (f j)) =
    CoordNode.one (f j) p.val at heq
  injection heq with hb

/-- Coherence of the actual infinite one map at every earlier
selected level, including arbitrary skipped ambient levels. -/
theorem infiniteOneCanonicalMap_truncate
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (i j : Nat) (hij : i ≤ j) (a : OneNode j) :
    (infiniteOneCanonicalMap h₁ h₂ j a).val.truncate (f i) =
      (infiniteOneCanonicalMap h₁ h₂ i (a.truncate i)).val := by
  have hmain :
      ∀ (j : Nat) (i : Nat) (hij : i ≤ j) (a : OneNode j),
      (infiniteOneCanonicalMap h₁ h₂ j a).val.truncate (f i) =
        (infiniteOneCanonicalMap h₁ h₂ i (a.truncate i)).val := by
    intro j
    induction j with
    | zero =>
        intro i hij a
        have hi : i = 0 := by omega
        subst i
        simp only [OneNode.truncate_self]
    | succ j ih =>
        intro i hij a
        by_cases heq : i = j + 1
        · subst i
          simp only [OneNode.truncate_self]
        · have hij0 : i ≤ j := by omega
          have hparent :=
            infiniteOneCanonicalMap_parent h₁ h₂ j a
          have hprev := ih i hij0 (a.truncate j)
          have hlevels : f i ≤ f j := hf.monotone hij0
          calc
            (infiniteOneCanonicalMap h₁ h₂ (j + 1) a).val.truncate (f i) =
              ((infiniteOneCanonicalMap h₁ h₂ (j + 1) a).val.truncate
                (f j)).truncate (f i) := by
                  symm
                  exact OneNode.truncate_truncate _ hlevels
            _ = (infiniteOneCanonicalMap h₁ h₂ j (a.truncate j)).val.truncate
                  (f i) := by
                    rw [hparent]
            _ = (infiniteOneCanonicalMap h₁ h₂ i ((a.truncate j).truncate i)).val :=
              hprev
            _ = (infiniteOneCanonicalMap h₁ h₂ i (a.truncate i)).val := by
                rw [a.truncate_truncate hij0]
  exact hmain j i hij a

end CoordNode
end ThreeUniformDiaries
