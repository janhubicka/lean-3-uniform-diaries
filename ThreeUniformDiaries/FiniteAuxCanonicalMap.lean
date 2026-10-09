import ThreeUniformDiaries.FiniteStrongTypedAuxLift

/-!
# The actual finite auxiliary canonical map

The previous module supplied the unique typed successor for a retained
auxiliary node at a selected level. Here we iterate that construction
for every finite source auxiliary type node of level i <= k.

The result is a concrete map AuxNode i -> AuxNode (f i), paired with a
proof that its image is in the completed finite strong picture. It
works even when the selected level f(0) is nonzero. This is not an
abstract record assuming canonical-map compatibility: each mapped
node is recursively constructed from the actual strong subtree.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The finite canonical auxiliary map induced by a strong picture
whose selected first-level root is the specified auxiliary node. -/
noncomputable def finiteStrongPicture_auxCanonicalMap
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r : AuxNode (f 0)}
    (hS : FiniteStrongPicture S f k (.aux (f 0) r)) :
    (i : Nat) → (hi : i ≤ k) → AuxNode i →
      {b : AuxNode (f i) // CoordNode.aux (f i) b ∈ S}
  | 0, _, _ => ⟨r, hS.2.2.1⟩
  | i + 1, hi, a => by
      have hik : i < k := by omega
      have hik0 : i ≤ k := by omega
      let prev :=
        finiteStrongPicture_auxCanonicalMap hS i hik0 (a.truncate i)
      let b := finiteStrongPicture_auxStep hS
        i hik prev.val prev.property (a.bit i)
      have hb :=
        (finiteStrongPicture_auxStep_spec hS
          i hik prev.val prev.property (a.bit i)).1
      exact ⟨b, hb⟩

/-- The first source level is sent to the chosen target root,
including when that root lives at a nonzero ambient level. -/
@[simp] theorem finiteStrongPicture_auxCanonicalMap_root
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r : AuxNode (f 0)}
    (hS : FiniteStrongPicture S f k (.aux (f 0) r))
    (a : AuxNode 0) :
    (finiteStrongPicture_auxCanonicalMap hS 0 (Nat.zero_le k) a).val = r :=
  rfl

end CoordNode
end ThreeUniformDiaries
