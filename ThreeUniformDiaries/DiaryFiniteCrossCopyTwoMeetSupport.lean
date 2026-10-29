import ThreeUniformDiaries.DiaryFiniteProtectedFactorization
import ThreeUniformDiaries.DiaryFiniteLeafMeetTwoSplitDisagreement

/-!
# Exact cross-copy full meets through finite induced support

A normal finite meet embedding protects numerical meets only
WITHIN one prescribed source copy. If two different source
copies share a genuine two-split vertex, however, their
cross-copy full leaf-pair meet can also be transported when
it occurs exactly at the shared image of that two-split.

The proof uses the genuine support inverse rank and the
verified finiteSupportGraph_twoMeet_exact_at_retained_twoSplit:
all earlier pair-type tests remain equal after restriction,
while the actual E3 disagreement at the retained two-split
survives induced copying. The support need not be convex,
and we make no false assertion about arbitrary cross-copy
meets or about a flip of the finite target.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Preserve an EXACT cross-copy pair meet through any finite
induced support containing both embedded source images.

The two original source diaries may be DIFFERENT genuine flips;
their maps are independently meet-preserving and only the
distinguished two-split images are required to coincide.
There is no assumption that either pair belongs to the other
source copy. -/
theorem finiteMeetEmbeddings_crossTwoMeet_through_support
    {A B G : Ordered3Graph Nat} {n : Nat}
    {f g : Nat → Nat}
    (DG : RoleDiary G)
    (Ei : FiniteMeetEmbedding A G n f)
    (Ej : FiniteMeetEmbedding B G n g)
    (S : Finset Nat)
    (hFi : ∀ u : Nat, u < n → f u ∈ S)
    (hGj : ∀ u : Nat, u < n → g u ∈ S)
    (s a b c d : Nat)
    (hsn : s < n)
    (hsa : s < a) (hsc : s < c)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (hs : IsTwoSplit A s)
    (hShared : f s = g s)
    (hCross : G.twoMeetLevel (f a) (f b) (g c) (g d) = f s) :
    (finiteSupportGraph G S).twoMeetLevel
        (finiteSupportLift S n f a) (finiteSupportLift S n f b)
        (finiteSupportLift S n g c) (finiteSupportLift S n g d) =
      finiteSupportLift S n f s := by
  classical
  have han : a < n := by omega
  have hcn : c < n := by omega
  have hMonoI : StrictMono (finiteSupportLift S n f) :=
    finiteSupportLift_strictMono S n f Ei.strictMono hFi
  have hMonoJ : StrictMono (finiteSupportLift S n g) :=
    finiteSupportLift_strictMono S n g Ej.strictMono hGj
  have hSharedNew : finiteSupportLift S n f s =
      finiteSupportLift S n g s := by
    rw [finiteSupportLift_of_lt S n f s hsn,
        finiteSupportLift_of_lt S n g s hsn,
        hShared]
  have hAB := hMonoI hab
  have hCD := hMonoJ hcd
  have hSA := hMonoI hsa
  have hSC : finiteSupportLift S n f s <
      finiteSupportLift S n g c := by
    rw [hSharedNew]
    exact hMonoJ hsc
  have hS := finiteSupportLift_spec S n f hFi s hsn
  have hA := finiteSupportLift_spec S n f hFi a han
  have hB := finiteSupportLift_spec S n f hFi b hbn
  have hC := finiteSupportLift_spec S n g hGj c hcn
  have hD := finiteSupportLift_spec S n g hGj d hdn
  have hSplitG : IsTwoSplit G (f s) :=
    (Ei.twoSplit_iff s hs.1 hsn).mpr hs
  have hSplitIndexed :
      IsTwoSplit G (finiteSupportIndex S
        (finiteSupportLift S n f s)) := by
    rw [hS.2]
    exact hSplitG
  have hCrossIndexed :
      G.twoMeetLevel
        (finiteSupportIndex S (finiteSupportLift S n f a))
        (finiteSupportIndex S (finiteSupportLift S n f b))
        (finiteSupportIndex S (finiteSupportLift S n g c))
        (finiteSupportIndex S (finiteSupportLift S n g d)) =
      finiteSupportIndex S (finiteSupportLift S n f s) := by
    rw [hA.2,hB.2,hC.2,hD.2,hS.2]
    exact hCross
  exact finiteSupportGraph_twoMeet_exact_at_retained_twoSplit
    (G := G) (S := S) DG
    (finiteSupportLift S n f a)
    (finiteSupportLift S n f b)
    (finiteSupportLift S n g c)
    (finiteSupportLift S n g d)
    (finiteSupportLift S n f s)
    hA.1 hB.1 hC.1 hD.1 hS.1
    hAB hCD hSA hSC
    hSplitIndexed hCrossIndexed

end DiaryLeafPriority
end ThreeUniformDiaries
