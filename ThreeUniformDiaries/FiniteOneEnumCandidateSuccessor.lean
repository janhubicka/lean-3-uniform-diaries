import ThreeUniformDiaries.FiniteSelectedSuccessorBridge
import ThreeUniformDiaries.FiniteSelectedSuccessorUnique
import ThreeUniformDiaries.FiniteActualCandidateMeetClosure

/-!
# Concrete singleton and enumeration steps for finite Aemb coding

The auxiliary coordinate's actual candidate step is verified in
FiniteAuxCandidateSuccessor. Here we prove the two analogous concrete
uniqueness statements for retained singleton and enumeration nodes.

At selected stage i the target candidate at f(i+1) is the unique
strong-picture descendant above the immediate successor of the
candidate at f(i), with parameter respectively
- the target auxiliary pair type (f(i), f(v)) over f(i),
- the target singleton type of f(i) over f(i).

The separate coupled canonical-map induction must identify these
parameters with the source parameters mapped through coordinates
T2 and T1. No new external type or edge assumptions are needed here.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem finiteOneCandidate_next_is_unique
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat) {S : Set CoordNode} {root : CoordNode}
    (hS : CoordNode.FiniteStrongPicture S f (m - 1) root)
    (hinc : ∀ x, finiteOneCandidate A H f n x → x ∈ S)
    (i v : Nat) (hni : n ≤ i) (hiv : i < v) (hvm : v < m) :
    ∀ z : CoordNode,
      z ∈ S →
      CoordNode.level z = f (i + 1) →
      CoordNode.one (f i + 1)
        ((H.oneType (f i) (f v)).succ
          (H.auxType (f i) (f i) (f v))) ≤ z →
      z = CoordNode.one (f (i + 1))
        (H.oneType (f (i + 1)) (f v)) := by
  have hik : i < m - 1 := by omega
  let p := CoordNode.one (f i) (H.oneType (f i) (f v))
  let t := CoordNode.one (f i + 1)
    ((H.oneType (f i) (f v)).succ
      (H.auxType (f i) (f i) (f v)))
  let q := CoordNode.one (f (i + 1))
    (H.oneType (f (i + 1)) (f v))
  have hp : p ∈ S := hinc p (Or.inr
    ⟨i, v, hni, Nat.le_of_lt hiv, hvm, rfl⟩)
  have hq : q ∈ S := hinc q (Or.inr
    ⟨i + 1, v, by omega, by omega, hvm, rfl⟩)
  have htq : t ≤ q := by
    have hlt : f i < f (i + 1) :=
      hf (Nat.lt_succ_self i)
    have hstep : f i + 1 ≤ f (i + 1) := by omega
    refine ⟨hstep, ?_⟩
    change CoordNode.one (f i + 1)
        ((H.oneType (f (i + 1)) (f v)).truncate (f i + 1)) =
      CoordNode.one (f i + 1)
        ((H.oneType (f i) (f v)).succ
          (H.auxType (f i) (f i) (f v)))
    exact congrArg (CoordNode.one (f i + 1))
      (finite_selected_one_successor H f hf i v)
  have hpt : p ≤ t := by
    refine ⟨by dsimp [p, t, CoordNode.level]; omega, ?_⟩
    simp [p, t, CoordNode.level, CoordNode.truncate]
  have hptCover : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpt
    change CoordNode.level t = CoordNode.level p + 1
    rfl
  rcases hS with ⟨_, _, _, _, _, _, hchildren⟩
  obtain ⟨z0, hz0, hunique⟩ :=
    hchildren i hik p hp rfl t hptCover
  intro z hz hzlev htz
  exact (hunique z ⟨hz, hzlev, htz⟩).trans
    (hunique q ⟨hq, rfl, htq⟩).symm

theorem finiteEnumCandidate_next_is_unique
    {N : Nat} (H : EnumNode N)
    (f : Nat → Nat) (hf : StrictMono f)
    (n m : Nat)
    {S : Set CoordNode} {root : CoordNode}
    (hS : CoordNode.FiniteStrongPicture S f (m - 1) root)
    (hinc : ∀ x, finiteEnumCandidate H f n m x → x ∈ S)
    (i : Nat) (hni : n ≤ i) (him : i + 1 < m) :
    ∀ z : CoordNode,
      z ∈ S →
      CoordNode.level z = f (i + 1) →
      CoordNode.enum (f i + 1)
        ((H.truncate (f i)).succ (H.oneType (f i) (f i))) ≤ z →
      z = CoordNode.enum (f (i + 1))
        (H.truncate (f (i + 1))) := by
  let p := CoordNode.enum (f i) (H.truncate (f i))
  let t := CoordNode.enum (f i + 1)
    ((H.truncate (f i)).succ (H.oneType (f i) (f i)))
  let q := CoordNode.enum (f (i + 1))
    (H.truncate (f (i + 1)))
  have hp : p ∈ S := hinc p (Or.inr
    ⟨i, hni, by omega, rfl⟩)
  have hq : q ∈ S := hinc q (Or.inr
    ⟨i + 1, by omega, him, rfl⟩)
  have htq : t ≤ q := by
    have hlt : f i < f (i + 1) :=
      hf (Nat.lt_succ_self i)
    have hstep : f i + 1 ≤ f (i + 1) := by omega
    refine ⟨hstep, ?_⟩
    change CoordNode.enum (f i + 1)
        ((H.truncate (f (i + 1))).truncate (f i + 1)) =
      CoordNode.enum (f i + 1)
        ((H.truncate (f i)).succ (H.oneType (f i) (f i)))
    exact congrArg (CoordNode.enum (f i + 1))
      (finite_selected_enum_successor H f hf i)
  have hpt : p ≤ t := by
    refine ⟨by dsimp [p, t, CoordNode.level]; omega, ?_⟩
    simp [p, t, CoordNode.level, CoordNode.truncate]
  have hptCover : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpt
    change CoordNode.level t = CoordNode.level p + 1
    rfl
  rcases hS with ⟨_, _, _, _, _, _, hchildren⟩
  obtain ⟨z0, hz0, hunique⟩ :=
    hchildren i (by omega) p hp rfl t hptCover
  intro z hz hzlev htz
  exact (hunique z ⟨hz, hzlev, htz⟩).trans
    (hunique q ⟨hq, rfl, htq⟩).symm

end EnumNode
end ThreeUniformDiaries
