import ThreeUniformDiaries.DiaryFiniteFlipTargetTransport
import ThreeUniformDiaries.DiaryFiniteMeetEmbedding

/-!
# Composing a leaf-only preembedding with a protected diary embedding

After a target diary B is flipped to B', a pre-existing finite
meet embedding A -> B becomes only a leaf preembedding A -> B':
the full mixed numerical meets may change.

To invoke the verified *countable* leaf-meet extraction theorem,
extend B' into a countable RoleDiary via an honest FiniteMeetEmbedding
B' -> G. This module proves that composition transports the
leaf-only preembedding, with exact singleton/full pair LEAF meets.

No unsupported claim about split-containing mixed meets is made.
The target bound is the value h(k), so images of every old source
vertex remain strictly below the bound in the countable target.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A B G : Ordered3Graph Nat}
variable {n k : Nat} {f h : Nat → Nat}

/-- Every source nonmarker maps above the three distinguished
target markers under a strictly increasing marker-fixing
finite leaf preembedding. -/
theorem FiniteLeafPreembedding.image_ge_three
    (P : FiniteLeafPreembedding A B n k f)
    (u : Nat) (hu3 : 3 ≤ u) : 3 ≤ f u := by
  have hTwo : f 2 < f u := P.strictMono (by omega : 2 < u)
  rw [P.marker_two] at hTwo
  omega

/-- Composition of a leaf preembedding with an actual mixed-meet
embedding remains a leaf preembedding, preserving exact LEAF
singleton/full pair meets, roles and induced leaf triples. -/
theorem FiniteLeafPreembedding.comp_meetEmbedding
    (P : FiniteLeafPreembedding A B n k f)
    (E : FiniteMeetEmbedding B G k h) :
    FiniteLeafPreembedding A G n (h k) (fun u => h (f u)) := by
  refine {
    strictMono := ?_
    marker_zero := ?_
    marker_one := ?_
    marker_two := ?_
    image_bound := ?_
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u v huv
    exact E.strictMono (P.strictMono huv)
  · rw [P.marker_zero,E.marker_zero]
  · rw [P.marker_one,E.marker_one]
  · rw [P.marker_two,E.marker_two]
  · intro u hun
    exact E.strictMono (P.image_bound u hun)
  · intro u hu3 hun
    have hfu3 : 3 ≤ f u := P.image_ge_three u hu3
    have hfun : f u < k := P.image_bound u hun
    obtain ⟨hl,ho,ht⟩ := P.role_iff u hu3 hun
    exact ⟨(E.leaf_iff (f u) hfu3 hfun).trans hl,
      (E.oneSplit_iff (f u) hfu3 hfun).trans ho,
      (E.twoSplit_iff (f u) hfu3 hfun).trans ht⟩
  · intro a b c hab hbc hcn ha hb hc
    have hLeaf := P.leaf_edge_iff a b c hab hbc hcn ha hb hc
    exact (E.edge_iff (f a) (f b) (f c)
      (P.strictMono hab) (P.strictMono hbc)
      (P.image_bound c hcn)).trans hLeaf
  · intro a b ha3 han hb3 hbn ha hb
    have hfu3 := P.image_ge_three a ha3
    have hfv3 := P.image_ge_three b hb3
    have hfun := P.image_bound a han
    have hfvn := P.image_bound b hbn
    calc
      G.oneMeetLevel (h (f a)) (h (f b)) =
          h (B.oneMeetLevel (f a) (f b)) :=
        E.oneMeet (f a) (f b) hfu3 hfun hfv3 hfvn
      _ = h (f (A.oneMeetLevel a b)) :=
        congrArg h (P.leaf_oneMeet a b ha3 han hb3 hbn ha hb)
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
      ha hb hc hd
    have hfa3 := P.image_ge_three a ha3
    have hfb3 := P.image_ge_three b hb3
    have hfc3 := P.image_ge_three c hc3
    have hfd3 := P.image_ge_three d hd3
    have hfan := P.image_bound a han
    have hfbn := P.image_bound b hbn
    have hfcn := P.image_bound c hcn
    have hfdn := P.image_bound d hdn
    calc
      G.twoMeetLevel (h (f a)) (h (f b)) (h (f c)) (h (f d)) =
          h (B.twoMeetLevel (f a) (f b) (f c) (f d)) :=
        E.twoMeet (f a) (f b) (f c) (f d)
          (P.strictMono hab) (P.strictMono hcd)
          hfa3 hfan hfb3 hfbn hfc3 hfcn hfd3 hfdn
      _ = h (f (A.twoMeetLevel a b c d)) :=
        congrArg h (P.leaf_twoMeet a b c d hab hcd
          ha3 han hb3 hbn hc3 hcn hd3 hdn ha hb hc hd)

end DiaryLeafPriority
end ThreeUniformDiaries
