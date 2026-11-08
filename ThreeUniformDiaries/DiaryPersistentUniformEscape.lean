import ThreeUniformDiaries.DiaryPersistentLeafEscapeDichotomy

/-!
# Track C: leaf-image escape is eventual at ALL later finite horizons

The verified persistent-next-leaf-or-escape dichotomy states that if
no compatible persistent next-leaf successor exists, then for any
numeric bound B there is SOME finite horizon N where all compatible
new leaf images exceed B. Genuine reserved-stage restriction
immediately upgrades this to EVERY later horizon n >= N.

Finite persistence of the old stage also provides an actual compatible
reserved witness at each later horizon, so the escape branch is
nonvacuous at every n >= N. This is stronger than merely saying that
arbitrarily large next-leaf image values can be chosen.

The result is a precise *obstruction*, not a proof that the escape
alternative is impossible for actual full diaries.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- If an old finitely persistent stage at a true new leaf has
no persistent compatible successor, then every sufficiently long
finite extension necessarily sends the new leaf beyond each fixed
numerical cutoff. There is at least one real compatible extension
at every such horizon (so the conclusion is nonvacuous). -/
theorem persistent_next_leaf_or_eventual_uniform_escape
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (P : PersistentReservedDiaryStage H K F m f) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ∨
    (∀ B : Nat, ∃ N : Nat,
      ∀ n : Nat, N ≤ n →
        (∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g) ∧
        (∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          B < g m)) := by
  rcases persistent_next_leaf_or_eventual_escape hm P with hGood | hEsc
  · exact Or.inl hGood
  · right
    intro B
    obtain ⟨N, _hNonemptyN, hEveryN⟩ := hEsc B
    refine ⟨N, ?_⟩
    intro n hn
    constructor
    · obtain ⟨g, Q, hOld⟩ := P.2 (n + 1)
      refine ⟨g, ?_, hOld⟩
      convert Q using 1 <;> omega
    · intro g Q hOld
      have QN : ReservedDiaryStage H K F (m + 1 + N) g :=
        Q.restrict (by omega)
      exact hEveryN g QN hOld

end DiaryLeafPriority
end ThreeUniformDiaries
