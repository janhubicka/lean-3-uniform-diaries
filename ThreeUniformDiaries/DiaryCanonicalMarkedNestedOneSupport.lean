import ThreeUniformDiaries.DiaryCanonicalMarkedNestedTwoMeet

/-!
# Nested marked-diary supports: the complete singleton-generator set

For L' ⊆ L genuine leaves of a full RoleDiary K, the exact S1
generator set on the selected ranks inside K_L is literally
the rank-image of the ambient S1 generator set for L'.

The proof uses the checked two-leaf S1 rank transport theorem,
and genuine injectivity of the finite rank on selected leaves.
It does not infer general type preservation for an arbitrary
finite compression, or any countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

theorem finiteOneMeetSupport_nested_rank_image
    {K : Ordered3Graph Nat}
    (D : RoleDiary K)
    (L L' : Finset Nat)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf K u)
    (hSub : L' ⊆ L) :
    (finiteOneMeetSupport K L').image
        (finiteSupportRank (finiteLeafMeetSupport K L)) =
      finiteOneMeetSupport
        (finiteSupportGraph K (finiteLeafMeetSupport K L))
        (L'.image (finiteSupportRank (finiteLeafMeetSupport K L))) := by
  classical
  let S : Finset Nat := finiteLeafMeetSupport K L
  let H : Ordered3Graph Nat := finiteSupportGraph K S
  let r : Nat → Nat := finiteSupportRank S
  have hInj {a b : Nat} (ha : a ∈ L') (hb : b ∈ L')
      (heq : r a = r b) : a = b := by
    have haS : a ∈ S := mem_finiteLeafMeetSupport_leaf K L a (hSub ha)
    have hbS : b ∈ S := mem_finiteLeafMeetSupport_leaf K L b (hSub hb)
    have hra := (finiteSupportRank_spec S a haS).2
    have hrb := (finiteSupportRank_spec S b hbS).2
    calc
      a = finiteSupportIndex S (r a) := hra.symm
      _ = finiteSupportIndex S (r b) :=
        congrArg (finiteSupportIndex S) heq
      _ = b := hrb
  apply Finset.ext
  intro t
  constructor
  · intro ht
    obtain ⟨m, hm, hmt⟩ := Finset.mem_image.mp ht
    change m ∈ ((L'.product L').filter
      (fun p : Nat × Nat => p.1 ≠ p.2)).image
        (fun p : Nat × Nat => K.oneMeetLevel p.1 p.2) at hm
    obtain ⟨p, hp, hpm⟩ := Finset.mem_image.mp hm
    rcases p with ⟨a,b⟩
    obtain ⟨hpProd, hab⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hpProd
    have haRank : r a ∈ L'.image r :=
      Finset.mem_image.mpr ⟨a,ha,rfl⟩
    have hbRank : r b ∈ L'.image r :=
      Finset.mem_image.mpr ⟨b,hb,rfl⟩
    have habRank : r a ≠ r b := by
      intro h
      exact hab (hInj ha hb h)
    have hPair : (r a,r b) ∈
        (((L'.image r).product (L'.image r)).filter
          (fun p : Nat × Nat => p.1 ≠ p.2)) :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨haRank,hbRank⟩,habRank⟩
    have hGen :
        H.oneMeetLevel (r a) (r b) ∈
          finiteOneMeetSupport H (L'.image r) := by
      change H.oneMeetLevel (r a) (r b) ∈
        (((L'.image r).product (L'.image r)).filter
          (fun p : Nat × Nat => p.1 ≠ p.2)).image
            (fun p : Nat × Nat => H.oneMeetLevel p.1 p.2)
      exact Finset.mem_image.mpr ⟨(r a,r b),hPair,rfl⟩
    have hNested :=
      finiteLeafMeetSupport_nested_rank_oneMeet D L hLeaves
        (hSub ha) (hSub hb) hab
    have hEq : H.oneMeetLevel (r a) (r b) = t :=
      hNested.trans ((congrArg r hpm).trans hmt)
    simpa only [hEq] using hGen
  · intro ht
    change t ∈
      (((L'.image r).product (L'.image r)).filter
        (fun p : Nat × Nat => p.1 ≠ p.2)).image
          (fun p : Nat × Nat => H.oneMeetLevel p.1 p.2) at ht
    obtain ⟨p,hp,hpt⟩ := Finset.mem_image.mp ht
    rcases p with ⟨u,v⟩
    obtain ⟨hpProd,huv⟩ := Finset.mem_filter.mp hp
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hpProd
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    have hab : a ≠ b := by
      intro h
      subst b
      exact huv rfl
    have hGen : K.oneMeetLevel a b ∈ finiteOneMeetSupport K L' := by
      change K.oneMeetLevel a b ∈ ((L'.product L').filter
        (fun p : Nat × Nat => p.1 ≠ p.2)).image
          (fun p : Nat × Nat => K.oneMeetLevel p.1 p.2)
      exact Finset.mem_image.mpr
        ⟨(a,b),Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hab⟩,rfl⟩
    have hNested :=
      finiteLeafMeetSupport_nested_rank_oneMeet D L hLeaves
        (hSub ha) (hSub hb) hab
    exact Finset.mem_image.mpr
      ⟨K.oneMeetLevel a b,hGen,hNested.symm.trans hpt⟩

end DiaryLeafPriority
end ThreeUniformDiaries
