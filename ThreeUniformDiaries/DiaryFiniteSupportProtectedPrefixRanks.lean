import ThreeUniformDiaries.DiaryFiniteSupportInverseRank

/-!
# Track B: keeping a complete numerical prefix prevents rank movement on compression

Finite-family joint embeddings are followed by leaf-meet finite support
extraction and increasing reindexing. The abstract compression need not
preserve every old numerical position: omitted support vertices shift
ranks. Here we isolate the sharp elementary positive repair.

If a finite support S contains EVERY numerical vertex below p,
then increasing enumeration and its inverse rank fix [0,p) LITERALLY.
Consequently a bounded finite copy already fixing the old prefix p
keeps that prefix pointwise fixed after rank compression, provided the
support contains the prefix. No global RoleDiary or hypothetical
relative finite absorber theorem is used.

This shifts the outstanding challenge upstream: construct the ambient
protected copy and select the support to contain its whole desired
prefix. Compression itself does not force protected prefix motion.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every existing old numerical vertex below a FULL supported prefix
has its literal rank. Crucially we use strictly increasing order on
the selected support; membership at one isolated index would not
suffice to preserve that index. -/
theorem finiteSupportRank_fixed_prefix
    (S : Finset Nat) (p : Nat)
    (hPrefix : ∀ u : Nat, u < p → u ∈ S) :
    ∀ i : Nat, i < p → finiteSupportRank S i = i := by
  intro i
  induction i with
  | zero =>
      intro h0
      have hSpec :=
        finiteSupportRank_spec S 0 (hPrefix 0 h0)
      have hGe :=
        finiteSupportIndex_ge_index S
          (finiteSupportRank S 0) hSpec.1
      rw [hSpec.2] at hGe
      omega
  | succ i ih =>
      intro hi
      have hiPrev : i < p := by omega
      have hiMem : i ∈ S := hPrefix i hiPrev
      have hiNext : i+1 ∈ S := hPrefix (i+1) hi
      have hStrict :=
        finiteSupportRank_lt S hiMem hiNext (by omega : i < i+1)
      have hSpec := finiteSupportRank_spec S (i+1) hiNext
      have hGe :=
        finiteSupportIndex_ge_index S
          (finiteSupportRank S (i+1)) hSpec.1
      rw [ih hiPrev] at hStrict
      rw [hSpec.2] at hGe
      omega

/-- The sorted enumeration of an induced support containing a
complete literal prefix agrees with the identity at every
index of that prefix, not just at the three markers. -/
theorem finiteSupportIndex_fixed_prefix
    (S : Finset Nat) (p : Nat)
    (hPrefix : ∀ u : Nat, u < p → u ∈ S)
    (i : Nat) (hi : i < p) :
    finiteSupportIndex S i = i := by
  have hSpec := finiteSupportRank_spec S i (hPrefix i hi)
  have hRank := finiteSupportRank_fixed_prefix S p hPrefix i hi
  rw [hRank] at hSpec
  exact hSpec.2

/-- Compression of an existing finite source copy does not undo
literal protection of its old prefix, as long as all those old
vertices are retained in the finite support. -/
theorem finiteSupportLift_fixed_prefix
    (S : Finset Nat) (n p : Nat) (f : Nat → Nat)
    (hp : p ≤ n)
    (hPrefix : ∀ u : Nat, u < p → u ∈ S)
    (hOldFix : ∀ u : Nat, u < p → f u = u) :
    ∀ u : Nat, u < p → finiteSupportLift S n f u = u := by
  intro u hu
  have hun : u < n := by omega
  rw [finiteSupportLift_of_lt S n f u hun, hOldFix u hu]
  exact finiteSupportRank_fixed_prefix S p hPrefix u hu

end DiaryLeafPriority
end ThreeUniformDiaries
