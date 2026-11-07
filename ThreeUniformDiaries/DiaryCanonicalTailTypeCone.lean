import ThreeUniformDiaries.DiaryReservedTailLeafReplacement

/-!
# A canonical finite type cone for replacing one selected new leaf

The general tail replacement theorem assumes a cut B above ALL
supported old and newly introduced nonleaf target images. Such
a cut is not a new mathematical hypothesis: the source support
is finite.

Define B to be one more than the maximum target image of
S_(m+1) with the newly selected leaf m erased. Then equality
of the two target leaf singleton types below this EXPLICIT
finite cut suffices for the full reserved stage replacement.

This packages the tail realization problem as membership in a
single concrete (mixed-ternary) unary type cone. Its nonemptiness
inside any prescribed unordered universal leaf copy is NOT proved.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The explicit cut above every supported target image other than
the newly chosen source leaf itself. -/
noncomputable def canonicalTailTypeCut
    (H : Ordered3Graph Nat) (m : Nat) (g0 : Nat → Nat) : Nat :=
  ((countableDiaryFiniteSupport H (m + 1)).erase m).sup g0 + 1

theorem supported_other_lt_canonicalTailTypeCut
    (H : Ordered3Graph Nat) (m : Nat) (g0 : Nat → Nat)
    (u : Nat)
    (hu : u ∈ countableDiaryFiniteSupport H (m + 1))
    (hum : u ≠ m) :
    g0 u < canonicalTailTypeCut H m g0 := by
  classical
  have huErase : u ∈
      (countableDiaryFiniteSupport H (m + 1)).erase m :=
    Finset.mem_erase.mpr ⟨hum,hu⟩
  have hBound : g0 u ≤
      ((countableDiaryFiniteSupport H (m + 1)).erase m).sup g0 :=
    Finset.le_sup (f := g0) huErase
  dsimp only [canonicalTailTypeCut]
  omega

/-- Any LATER target leaf of the ORIGINAL F-range in the SAME
old-support mixed singleton-type cone can replace a genuine new
source leaf without changing the rest of the supported image. -/
theorem ReservedDiaryStage.replace_new_leaf_in_canonical_type_cone
    {H K : Ordered3Graph Nat} {F g0 : Nat → Nat}
    {m v : Nat}
    (hm : IsLeaf H m)
    (P : ReservedDiaryStage H K F (m + 1) g0)
    (hTail : K.SameOneTypeBelow
      (canonicalTailTypeCut H m g0) (g0 m) v)
    (hvLater : g0 m ≤ v)
    (hvLeaf : IsLeaf K v)
    (hvRange : ∃ t : Nat, v = F t) :
    ReservedDiaryStage H K F (m + 1)
      (replaceAt g0 m v) := by
  apply ReservedDiaryStage.replace_new_leaf_of_same_tail_type
    hm P ?_ hTail hvLater hvLeaf hvRange
  intro u hu hum
  exact supported_other_lt_canonicalTailTypeCut H m g0 u hu hum

end DiaryLeafPriority
end ThreeUniformDiaries
