import ThreeUniformDiaries.DiaryCountableRelativeStepExtension

/-!
# The inverse system of genuine finite diary support maps

The cofinal supports S_m are nested, and every admissible map on S_n
automatically restricts to a valid admissible map on S_m for m≤n.
This is the precise "forgetful map" needed to formulate the remaining
relative-extension / fusion problem as an inverse system. We also
isolate the overlap-equality relation and its transitivity.

No extension or infinite coherent path is asserted. In particular,
surjectivity of these restriction maps is NOT proved from finite
flip absorption, and cannot be inferred from finite-stage nonemptiness.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

namespace AdmissibleCofinalDiaryStage

variable {H K : Ordered3Graph Nat} {F : Nat → Nat}

/-- Restrict a supplied *genuine* finite stage map to an earlier
canonical leaf-meet support. No images are changed. -/
theorem restrict
    {m n : Nat} {f : Nat → Nat}
    (P : AdmissibleCofinalDiaryStage H K F n f)
    (hmn : m ≤ n) :
    AdmissibleCofinalDiaryStage H K F m f := by
  have hSub : ∀ u : Nat,
      u ∈ countableDiaryFiniteSupport H m →
      u ∈ countableDiaryFiniteSupport H n :=
    fun u hu => countableDiaryFiniteSupport_mono H m n hmn hu
  refine {
    ordered := ?_
    marker_zero := P.marker_zero
    marker_one := P.marker_one
    marker_two := P.marker_two
    leaf_role := ?_
    one_split_role := ?_
    two_split_role := ?_
    induced_edge := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
    leaf_range := ?_
  }
  · intro u v hu hv huv
    exact P.ordered u v (hSub u hu) (hSub v hv) huv
  · intro u hu hLeaf
    exact P.leaf_role u (hSub u hu) hLeaf
  · intro u hu hOne
    exact P.one_split_role u (hSub u hu) hOne
  · intro u hu hTwo
    exact P.two_split_role u (hSub u hu) hTwo
  · intro a b c ha hb hc hab hbc
    exact P.induced_edge a b c
      (hSub a ha) (hSub b hb) (hSub c hc) hab hbc
  · intro a b ha hb hLa hLb
    exact P.leaf_oneMeet a b (hSub a ha) (hSub b hb) hLa hLb
  · intro a b c d ha hb hc hd hab hcd hLa hLb hLc hLd
    exact P.leaf_twoMeet a b c d
      (hSub a ha) (hSub b hb) (hSub c hc) (hSub d hd)
      hab hcd hLa hLb hLc hLd
  · intro u hu hLeaf
    exact P.leaf_range u (hSub u hu) hLeaf

end AdmissibleCofinalDiaryStage

/-- The later map literally agrees with the earlier map on
the previous entire finite support. No relabeling, flip, or
postcomposition by a target automorphism is allowed. -/
def CofinalDiaryStageCompatible
    (H : Ordered3Graph Nat) (m : Nat)
    (f g : Nat → Nat) : Prop :=
  ∀ u : Nat, u ∈ countableDiaryFiniteSupport H m → g u = f u

namespace CofinalDiaryStageCompatible

variable {H : Ordered3Graph Nat}
variable {f g h : Nat → Nat} {m n : Nat}

theorem refl (f : Nat → Nat) (m : Nat) :
    CofinalDiaryStageCompatible H m f f := by
  intro u _
  rfl

/-- Compatibility with a later map also holds on any
earlier, smaller support. -/
theorem restrict
    (hmn : m ≤ n)
    (hCompat : CofinalDiaryStageCompatible H n f g) :
    CofinalDiaryStageCompatible H m f g := by
  intro u hu
  exact hCompat u
    (countableDiaryFiniteSupport_mono H m n hmn hu)

/-- Compose two consecutive compatibility equations, even
when the second agreement is required on a larger support. -/
theorem trans
    (hmn : m ≤ n)
    (hFG : CofinalDiaryStageCompatible H m f g)
    (hGH : CofinalDiaryStageCompatible H n g h) :
    CofinalDiaryStageCompatible H m f h := by
  intro u hu
  exact (hGH u
    (countableDiaryFiniteSupport_mono H m n hmn hu)).trans (hFG u hu)

end CofinalDiaryStageCompatible
end DiaryLeafPriority
end ThreeUniformDiaries
