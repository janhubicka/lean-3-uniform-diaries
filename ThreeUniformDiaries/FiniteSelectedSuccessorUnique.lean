import ThreeUniformDiaries.FiniteStrongCompletion

/-!
# Unique next selected node in an arbitrary finite strong picture

The concrete finite converse Aemb construction produces three
FiniteStrongPicture objects on a shared strictly increasing level
map. This lemma spells out the exact consequence needed by the
manuscript's simultaneous canonical-map induction:

if p and q are retained nodes at consecutive selected levels with
p ≤ q, the first ambient successor t of p below q uniquely
determines q among all selected nodes at the next level.

Combined with the three equations in FiniteSelectedSuccessorBridge,
this is the local uniqueness ingredient for the selected-step
canonical-map identities. It does not yet construct f_i^S or F_I^S.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- A retained pair of nodes at adjacent *selected* levels is uniquely
identified by the one ambient child cone it follows. -/
theorem finiteStrongPicture_selectedSuccessorUnique
    {S : Set CoordNode} {lambda : Nat → Nat} {k : Nat}
    {root : CoordNode}
    (hS : FiniteStrongPicture S lambda k root)
    (hmono : StrictMono lambda)
    (i : Nat) (hi : i < k)
    (p q : CoordNode)
    (hp : p ∈ S) (hpl : level p = lambda i)
    (hq : q ∈ S) (hql : level q = lambda (i + 1))
    (hpq : p ≤ q) :
    ∃ t : CoordNode,
      p ⋖ t ∧ t ≤ q ∧
        ∀ z : CoordNode,
          z ∈ S → level z = lambda (i + 1) →
          t ≤ z → z = q := by
  rcases hS with ⟨_, _, _, _, _, _, hchildren⟩
  have hstep : lambda i + 1 ≤ lambda (i + 1) :=
    Nat.succ_le_of_lt (hmono (Nat.lt_succ_self i))
  let t := truncate q (lambda i + 1)
  have htl : level t = lambda i + 1 := by
    simp [t]
  have htq : t ≤ q := by
    apply truncate_le q
    rw [hql]
    exact hstep
  have hpt : p ≤ t := by
    refine ⟨?_, ?_⟩
    · rw [hpl, htl]
      omega
    · change truncate t (level p) = p
      calc
        truncate t (level p) =
            truncate q (level p) := by
          dsimp [t]
          exact truncate_truncate q (by rw [hpl]; omega)
        _ = p := hpq.2
  have hptCover : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpt
    change level t = level p + 1
    rw [htl, hpl]
  obtain ⟨z0, hz0, hunique⟩ :=
    hchildren i hi p hp hpl t hptCover
  refine ⟨t, hptCover, htq, ?_⟩
  intro z hz hzlevel htz
  exact (hunique z ⟨hz, hzlevel, htz⟩).trans
    (hunique q ⟨hq, hql, htq⟩).symm

end CoordNode
end ThreeUniformDiaries
