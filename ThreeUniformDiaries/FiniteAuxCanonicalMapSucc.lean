import ThreeUniformDiaries.FiniteAuxCanonicalMap

/-!
# The recursive auxiliary canonical map follows every prescribed bit

This proves the key geometric law: taking the source auxiliary
successor with bit e, then mapping to the next selected level, lands
in the immediate target child cone determined by the *same* bit
at the previously selected target level.

The map here is actually recursively constructed from a finite strong
picture; no compatibility field of an abstract CanonicalMap is assumed.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finiteStrongPicture_auxCanonicalMap_succ
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r : AuxNode (f 0)}
    (hS : FiniteStrongPicture S f k (.aux (f 0) r))
    (i : Nat) (hi : i < k) (a : AuxNode i) (bit : Bool) :
    CoordNode.aux (f i + 1)
      ((finiteStrongPicture_auxCanonicalMap hS i
        (Nat.le_of_lt hi) a).val.succ bit) ≤
    CoordNode.aux (f (i + 1))
      ((finiteStrongPicture_auxCanonicalMap hS (i + 1)
        (by omega) (a.succ bit)).val) := by
  let old := finiteStrongPicture_auxCanonicalMap hS i
    (Nat.le_of_lt hi) a
  have hstep :=
    (finiteStrongPicture_auxStep_spec hS i hi
      old.val old.property bit).2
  have heq :
      (finiteStrongPicture_auxCanonicalMap hS (i + 1)
        (by omega) (a.succ bit)).val =
      finiteStrongPicture_auxStep hS i hi
        old.val old.property bit := by
    dsimp only [finiteStrongPicture_auxCanonicalMap]
    simp only [AuxNode.truncate_succ, AuxNode.succ_new]
    rfl
  change CoordNode.aux (f i + 1) (old.val.succ bit) ≤
    CoordNode.aux (f (i + 1))
      ((finiteStrongPicture_auxCanonicalMap hS (i + 1)
        (by omega) (a.succ bit)).val)
  rw [heq]
  exact hstep

end CoordNode
end ThreeUniformDiaries
