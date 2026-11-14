import ThreeUniformDiaries.DiaryCofinalJointFiniteColourPersistence

/-!
# Track A: cofinally recurrent complete old-cut colour EXCLUDES bounded leaves

English-first adversarial proof: 3-uniform-diaries PR #358.

The previously kernel-checked full RoleDiary colour rigidity theorem
says that a genuine leaf u with u≤B is uniquely identified among
genuine leaves by its COMPLETE mixed singleton colour at cut B.

Therefore a complete c-colour class recurring on arbitrarily HIGH
genuine target leaves cannot contain ANY genuine leaf u≤B.

This is the exact boundary of the recent merged all-horizon
old-cut colour diagonal #1502: a cofinally recurring colour below
the OLD support cut is a fixed TYPE, not a fixed numerical NEW
leaf image. The fixed-new-image criterion in the checked
DiaryCofinalJointFiniteColourPersistence requires a larger cut
B' that includes the specifically chosen new leaf u≤B'.

No genericity, target F monotonicity, source diary, persistent
successor or countable unavoidability assumption is required.
The theorem does NOT rule out a persistent new image above B.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Under full target diary axioms, if one complete mixed singleton
colour c at finite cut B recurs on arbitrarily high ACTUAL target
leaves F(t), then NO genuine target leaf u≤B has that colour.

This is the direct consequence of the already checked
singletonColour_eq_iff_leaf_eq_above_self rigidity theorem.
It distinguishes cofinal old-cut type recurrence from equality
of a fixed new target leaf image. -/
theorem RoleDiary.cofinal_singletonColour_excludes_bounded_genuine_leaf
    {K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (F : Nat → Nat)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (B : Nat)
    (c : Fin B → Fin B → Bool)
    (hCofinal : ∀ M : Nat,
      ∃ t : Nat,
        M < F t ∧
        DiaryLowerBoundColors.singletonColour K B (F t) = c) :
    ∀ u : Nat, IsLeaf K u → u ≤ B →
      DiaryLowerBoundColors.singletonColour K B u ≠ c := by
  intro u hu huB hColourU
  obtain ⟨t, hHigh, hColourT⟩ := hCofinal B
  have hSame :
      DiaryLowerBoundColors.singletonColour K B u =
        DiaryLowerBoundColors.singletonColour K B (F t) :=
    hColourU.trans hColourT.symm
  have hEq : u = F t :=
    (DK.singletonColour_eq_iff_leaf_eq_above_self
      hu (hFLeaf t) huB).mp hSame
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
