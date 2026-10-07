import Milliken.MillikenTheorem

/-!
# Checked dependency on the verified Milliken development

The manuscript uses a vector-tree form of Milliken for finitely branching
trees.  The existing `lean-milliken` library currently exposes the
homogeneous-tree theorem.  This module records the verified dependency while
the vector-tree transport is formalized separately.
-/

namespace ThreeUniformDiaries

universe u

/-- The unconditional homogeneous-tree Milliken theorem from the dependency
is available with its published Abstract Ellentuck proof. -/
theorem homogeneousMillikenAvailable
    (ι : Type u) [Finite ι] [Nonempty ι] :
    RamseySpace.IsTopologicalRamseySpace
      (Milliken.Chapter6.abstractRamseySpace (ι := ι)) :=
  Milliken.Chapter6.milliken

end ThreeUniformDiaries
