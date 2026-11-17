import ThreeUniformDiaries.DiaryCanonicalMarkedNestedOneSupport

/-!
# Nested marked-diary supports: the complete ordered-pair S2 generators

For genuine selected leaves L'⊆L, the complete full S2 generator
set after reindexing the larger canonical diary is the
rank-image of the original S2 generators in K.

Both directions use actual finite witnesses (ordered leaf pairs),
and order reflection is proved from the increasing rank enumeration.
The proof covers common-first-leaf caps and marker 1 explicitly
through the previously checked full twoMeet rank identity.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

theorem finiteTwoMeetSupport_nested_rank_image
    {K : Ordered3Graph Nat}
    (D : RoleDiary K)
    (L L' : Finset Nat)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf K u)
    (hSub : L' ⊆ L) :
    (finiteTwoMeetSupport K L').image
        (finiteSupportRank (finiteLeafMeetSupport K L)) =
      finiteTwoMeetSupport
        (finiteSupportGraph K (finiteLeafMeetSupport K L))
        (L'.image (finiteSupportRank (finiteLeafMeetSupport K L))) := by
  classical
  let S : Finset Nat := finiteLeafMeetSupport K L
  let H : Ordered3Graph Nat := finiteSupportGraph K S
  let r : Nat → Nat := finiteSupportRank S
  have hSelected (u : Nat) (hu : u ∈ L') :
      u ∈ S := mem_finiteLeafMeetSupport_leaf K L u (hSub hu)
  have hRankOrder {a b : Nat} (ha : a ∈ L') (hb : b ∈ L')
      (h : r a < r b) : a < b := by
    have hra := finiteSupportRank_spec S a (hSelected a ha)
    have hrb := finiteSupportRank_spec S b (hSelected b hb)
    have hIncl := finiteSupportIndex_strictMono S (r a) (r b) h hrb.1
    simpa only [hra.2,hrb.2] using hIncl
  have hRankPair (a b : Nat)
      (ha : a ∈ L') (hb : b ∈ L') (hab : a < b) :
      (r a,r b) ∈ finiteOrderedLeafPairs (L'.image r) := by
    have hrAB : r a < r b :=
      finiteSupportRank_lt S (hSelected a ha) (hSelected b hb) hab
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨a,ha,rfl⟩,
         Finset.mem_image.mpr ⟨b,hb,rfl⟩⟩,hrAB⟩
  apply Finset.ext
  intro t
  constructor
  · intro ht
    obtain ⟨m,hm,hmt⟩ := Finset.mem_image.mp ht
    change m ∈ ((finiteOrderedLeafPairs L').product
      (finiteOrderedLeafPairs L')).image
        (fun p : (Nat × Nat) × (Nat × Nat) =>
          K.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2) at hm
    obtain ⟨p,hp,hpm⟩ := Finset.mem_image.mp hm
    rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩
    obtain ⟨habPair,hcdPair⟩ := Finset.mem_product.mp hp
    obtain ⟨habProd,hab⟩ := Finset.mem_filter.mp habPair
    obtain ⟨hcdProd,hcd⟩ := Finset.mem_filter.mp hcdPair
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp habProd
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcdProd
    have hrAB := hRankPair a b ha hb hab
    have hrCD := hRankPair c d hc hd hcd
    have hGen :
        H.twoMeetLevel (r a) (r b) (r c) (r d) ∈
          finiteTwoMeetSupport H (L'.image r) := by
      change H.twoMeetLevel (r a) (r b) (r c) (r d) ∈
        ((finiteOrderedLeafPairs (L'.image r)).product
          (finiteOrderedLeafPairs (L'.image r))).image
            (fun p : (Nat × Nat) × (Nat × Nat) =>
              H.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2)
      exact Finset.mem_image.mpr
        ⟨((r a,r b),(r c,r d)),
          Finset.mem_product.mpr ⟨hrAB,hrCD⟩,rfl⟩
    have hNested :=
      finiteLeafMeetSupport_nested_rank_twoMeet D L hLeaves
        hab hcd (hSub ha) (hSub hb) (hSub hc) (hSub hd)
    have hEq : H.twoMeetLevel (r a) (r b) (r c) (r d) = t :=
      hNested.trans ((congrArg r hpm).trans hmt)
    simpa only [hEq] using hGen
  · intro ht
    change t ∈
      ((finiteOrderedLeafPairs (L'.image r)).product
        (finiteOrderedLeafPairs (L'.image r))).image
          (fun p : (Nat × Nat) × (Nat × Nat) =>
            H.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2) at ht
    obtain ⟨p,hp,hpt⟩ := Finset.mem_image.mp ht
    rcases p with ⟨⟨u,v⟩,⟨x,y⟩⟩
    obtain ⟨huvPair,hxyPair⟩ := Finset.mem_product.mp hp
    obtain ⟨huvProd,huv⟩ := Finset.mem_filter.mp huvPair
    obtain ⟨hxyProd,hxy⟩ := Finset.mem_filter.mp hxyPair
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp huvProd
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxyProd
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hy
    have hab : a < b := hRankOrder ha hb huv
    have hcd : c < d := hRankOrder hc hd hxy
    have hAB : (a,b) ∈ finiteOrderedLeafPairs L' :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hab⟩
    have hCD : (c,d) ∈ finiteOrderedLeafPairs L' :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hc,hd⟩,hcd⟩
    have hGen : K.twoMeetLevel a b c d ∈
        finiteTwoMeetSupport K L' := by
      change K.twoMeetLevel a b c d ∈
        ((finiteOrderedLeafPairs L').product
          (finiteOrderedLeafPairs L')).image
            (fun p : (Nat × Nat) × (Nat × Nat) =>
              K.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2)
      exact Finset.mem_image.mpr
        ⟨((a,b),(c,d)),Finset.mem_product.mpr ⟨hAB,hCD⟩,rfl⟩
    have hNested :=
      finiteLeafMeetSupport_nested_rank_twoMeet D L hLeaves
        hab hcd (hSub ha) (hSub hb) (hSub hc) (hSub hd)
    exact Finset.mem_image.mpr
      ⟨K.twoMeetLevel a b c d,hGen,hNested.symm.trans hpt⟩

end DiaryLeafPriority
end ThreeUniformDiaries
