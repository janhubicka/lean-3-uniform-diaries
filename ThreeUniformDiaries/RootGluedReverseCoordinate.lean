import ThreeUniformDiaries.RootGluedActualFiniteApprox
import Milliken.GeneralTree.Ancestry

/-!
# Extract genuine E0/E1/E2 coordinates from an arbitrary scalar strong tree

This is the non-tautological reverse direction needed when Milliken
returns a scalar strong subtree of the *actual* rooted type tree.

A selected level-one root is unique in each of the three sort cones.
Inside every coordinate, the scalar successor-uniqueness axiom becomes
the exact successor-cone axiom for the corresponding ATR type tree.
The remaining reverse obligations are root ancestry, meets and
componentwise level population, proved separately; none is assumed here.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The slice in one of the three actual type-tree sorts. -/
def millikenCoordinateSlice
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (i : Fin 3) : Set CoordNode :=
  (TypedVectorSubset.ofGlued S.carrier).carrier i

@[simp] theorem mem_millikenCoordinateSlice_iff
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (i : Fin 3) (x : CoordNode) :
    x ∈ millikenCoordinateSlice S i ↔
      sort x = i ∧ (some x : WithBot CoordNode) ∈ S.carrier :=
  Iff.rfl

/-- Every coordinate root cone contributes precisely one node on the
first positive selected scalar level, with no global degree bound. -/
theorem millikenCoordinate_unique_first_root
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (f : Nat → Nat)
    (hlevels : S.levels = selectedGluedLevels f)
    (t : CoordNode) (ht : level t = 0) :
    ∃! r : CoordNode,
      r ∈ millikenCoordinateSlice S (sort t) ∧
        level r = f 0 := by
  have hzero : S.levels 0 = 0 := by
    rw [hlevels, selectedGluedLevels_zero]
  have hroot : S.root = (none : WithBot CoordNode) :=
    millikenStrong_root_eq_gluedRoot S hzero
  have hrootmem : (none : WithBot CoordNode) ∈ S.carrier := by
    have hr := S.root_mem
    rw [hroot] at hr
    exact hr
  have hrootlevel :
      rootGluedAmbientTree.level (none : WithBot CoordNode) =
        S.levels 0 := by
    rw [hlevels, selectedGluedLevels_zero]
    exact rootGluedAmbientTree.level_root
  have hchild :
      (none : WithBot CoordNode) ⋖ (some t : WithBot CoordNode) :=
    (gluedChild_iff_covBy _ _).mp ht
  obtain ⟨z, hz, hunique⟩ :=
    S.successor_unique 0 (none : WithBot CoordNode)
      hrootmem hrootlevel (some t : WithBot CoordNode) hchild
  cases z with
  | none =>
      exact False.elim
        (WithBot.not_coe_le_bot t hz.2.2)
  | some r =>
      have hrlevel : level r = f 0 := by
        have hlev := hz.2.1
        rw [hlevels, selectedGluedLevels_succ] at hlev
        have hrank := rootGluedAmbient_level_coe r
        omega
      have hrsort : sort r = sort t :=
        (sort_eq_of_le (WithBot.coe_le_coe.mp hz.2.2)).symm
      refine ⟨r, ⟨⟨hrsort, hz.1⟩, hrlevel⟩, ?_⟩
      intro s hs
      have hssort : sort s = sort t := hs.1.1
      have hst : t ≤ s :=
        zero_node_le_of_same_sort t s ht hssort.symm
      have hslevel :
          rootGluedAmbientTree.level (some s : WithBot CoordNode) =
            S.levels 1 := by
        rw [hlevels, selectedGluedLevels_succ]
        have hrank := rootGluedAmbient_level_coe s
        omega
      have heq : (some s : WithBot CoordNode) = some r :=
        hunique (some s)
          ⟨hs.1.2, hslevel, WithBot.coe_le_coe.mpr hst⟩
      exact Option.some.inj heq

/-- The actual next selected level in a scalar Milliken tree yields
the unique selected representative in every ambient E_i child cone.
This is precisely the successor field of InfiniteStrongPicture. -/
theorem millikenCoordinate_next_child
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (f : Nat → Nat)
    (hlevels : S.levels = selectedGluedLevels f)
    (i : Fin 3) (j : Nat)
    (p : CoordNode)
    (hp : p ∈ millikenCoordinateSlice S i)
    (hpLevel : level p = f j)
    (t : CoordNode) (hpt : p ⋖ t) :
    ∃! q : CoordNode,
      q ∈ millikenCoordinateSlice S i ∧
        level q = f (j + 1) ∧ t ≤ q := by
  have hpx : (some p : WithBot CoordNode) ∈ S.carrier := hp.2
  have hplevel :
      rootGluedAmbientTree.level (some p : WithBot CoordNode) =
        S.levels (j + 1) := by
    rw [hlevels, selectedGluedLevels_succ]
    have hrank := rootGluedAmbient_level_coe p
    omega
  have hchild :
      (some p : WithBot CoordNode) ⋖ (some t : WithBot CoordNode) :=
    (gluedChild_iff_covBy _ _).mp hpt
  obtain ⟨z, hz, hunique⟩ :=
    S.successor_unique (j + 1) (some p : WithBot CoordNode)
      hpx hplevel (some t : WithBot CoordNode) hchild
  cases z with
  | none =>
      exact False.elim
        (WithBot.not_coe_le_bot t hz.2.2)
  | some q =>
      have hqlevel : level q = f (j + 1) := by
        have hlev := hz.2.1
        rw [hlevels, selectedGluedLevels_succ] at hlev
        have hrank := rootGluedAmbient_level_coe q
        omega
      have hqi : sort q = i := by
        have htp : sort p = sort t := sort_eq_of_le hpt.le
        have htq : sort t = sort q :=
          sort_eq_of_le (WithBot.coe_le_coe.mp hz.2.2)
        exact htq.symm.trans (htp.symm.trans hp.1)
      refine ⟨q, ⟨⟨hqi, hz.1⟩, hqlevel, WithBot.coe_le_coe.mp hz.2.2⟩, ?_⟩
      intro q' hq'
      have hq'level :
          rootGluedAmbientTree.level (some q' : WithBot CoordNode) =
            S.levels ((j + 1) + 1) := by
        rw [hlevels, selectedGluedLevels_succ]
        have hrank := rootGluedAmbient_level_coe q'
        omega
      have heq : (some q' : WithBot CoordNode) = some q :=
        hunique (some q')
          ⟨hq'.1.2, hq'level, WithBot.coe_le_coe.mpr hq'.2.2⟩
      exact Option.some.inj heq

end CoordNode
end ThreeUniformDiaries
