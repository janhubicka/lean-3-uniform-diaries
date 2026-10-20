import ThreeUniformDiaries.DiaryFlipCausalFixedPoint
import Mathlib

/-!
# Causal flip correction on a finite INVARIANT family

The active split-control vectors of a finite diary need NOT form
the entire free Boolean cube. The two 1-split controls in the
nine-vertex diary of the root-obstruction example are coupled:
a genuine flip preserving the leaf-pair meet at 3 must switch
them together.

The elementary correction argument can be repaired at an
ABSTRACT level. A triangular XOR transformation
  R(x)_i = x_i xor noise(x)_i
is injective on the whole Boolean cube whenever noise at i
depends only on coordinates earlier than i. If R maps a
NONEMPTY finite set S of REALISABLE flip words into itself,
then R is automatically a permutation of S. Hence every
prescribed element of S (in particular the baseline word)
has a predecessor in S.

Unlike the earlier free-cube fixed-point argument, this
lemma never assumes that arbitrary bit words are genuine
diary flips. The crucial remaining geometric task is to
construct an actual family whose induced pullback feedback
has this triangular form and whose image stays inside
the realised flip family. The latter closure is available
abstractly from the verified canonical target-flip pullback,
but no geometric causality proof is claimed here.
-/

namespace ThreeUniformDiaries
namespace FlipGuidedBranch

/-- The triangular XOR transformation associated with a
prefix-dependent correction word. -/
def xorFeedback
    (n : Nat) (noise : (Fin n → Bool) → (Fin n → Bool))
    (w : Fin n → Bool) : Fin n → Bool :=
  fun i => Bool.xor (w i) (noise w i)

/-- Triangular XOR corrections are injective on the full cube.
The proof is by induction over the coordinates: agreement at
earlier coordinates makes the noise bits equal, so equality
of the corrected bits cancels their common noise. -/
theorem xorFeedback_injective
    (n : Nat)
    (noise : (Fin n → Bool) → (Fin n → Bool))
    (hCausal : StrictlyPrefixCausal n noise) :
    Function.Injective (xorFeedback n noise) := by
  intro x y hxy
  funext i
  have hAll :
      ∀ m : Nat, ∀ j : Fin n, j.val = m → x j = y j := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro j hj
      have hPrior : ∀ k : Fin n, k.val < j.val → x k = y k := by
        intro k hk
        exact ih k.val (by omega) k rfl
      have hNoise : noise x j = noise y j :=
        hCausal x y j hPrior
      have hAt := congrFun hxy j
      change Bool.xor (x j) (noise x j) =
        Bool.xor (y j) (noise y j) at hAt
      rw [← hNoise] at hAt
      cases hx : x j <;>
        cases hy : y j <;>
        cases hn : noise x j <;>
        simp_all [Bool.xor]
  exact hAll i.val i rfl

/-- A finite subset invariant under an injective map is
permuted by that map. Every vertex in the subset has an
actual predecessor which is also in the subset. -/
theorem exists_preimage_in_invariant_finset
    {α : Type*} [DecidableEq α]
    (S : Finset α) (F : α → α)
    (hinj : Function.Injective F)
    (hClosed : ∀ x : α, x ∈ S → F x ∈ S)
    (z : α) (hz : z ∈ S) :
    ∃ x : α, x ∈ S ∧ F x = z := by
  classical
  let e : {x : α // x ∈ S} → {x : α // x ∈ S} :=
    fun x => ⟨F x.val,hClosed x.val x.property⟩
  have heinj : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hxy)
  have hesurj : Function.Surjective e :=
    (Finite.injective_iff_surjective).mp heinj
  obtain ⟨x,hx⟩ := hesurj ⟨z,hz⟩
  exact ⟨x.val,x.property,congrArg Subtype.val hx⟩

/-- Finite constrained-flip correction: if a strictly
causal XOR pullback sends ALL REALISABLE source flip words
back into the same finite set, it has a predecessor of
the baseline word INSIDE that set.

This does NOT assume arbitrary Boolean vectors are flips.
The theorem is conditional on the actual flip-family
invariance and geometric causal feedback hypotheses. -/
theorem exists_causal_correction_in_invariant_family
    (n : Nat)
    (S : Finset (Fin n → Bool))
    (noise : (Fin n → Bool) → (Fin n → Bool))
    (hCausal : StrictlyPrefixCausal n noise)
    (baseline : Fin n → Bool) (hBaseline : baseline ∈ S)
    (hClosed : ∀ w : Fin n → Bool, w ∈ S →
       xorFeedback n noise w ∈ S) :
    ∃ w : Fin n → Bool,
      w ∈ S ∧ xorFeedback n noise w = baseline := by
  classical
  exact exists_preimage_in_invariant_finset S
    (xorFeedback n noise)
    (xorFeedback_injective n noise hCausal)
    hClosed baseline hBaseline

end FlipGuidedBranch
end ThreeUniformDiaries
