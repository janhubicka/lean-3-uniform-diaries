import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection

/-!
# What survives a flip of the target of a finite diary embedding

Suppose an honest finite meet embedding e:A -> B has its entire
bounded source image inside a finite diary B. If B' is any flip
of B, composing e with the identity-on-vertices flip does NOT
necessarily give a diary embedding A -> B'. In particular its
split-positive incidence bits may change.

Nevertheless it always gives a genuine diary PRE-embedding
on leaf data:
* strict increase and all three markers;
* reflected leaf/one-split/two-split roles;
* the induced leaf-only ternary relation;
* exact singleton and full ordered-pair meets of source LEAVES.

This is the missing safe first interface for pulling back a
target flip. It makes NO assertion that the pulled-back finite
structure is already a diary, or that an appropriate compensating
source flip has been chosen.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The precise finite leaf-pre-embedding data surviving an
arbitrary target flip. Strong mixed-meet preservation is NOT
part of this interface. -/
structure FiniteLeafPreembedding
    (A T : Ordered3Graph Nat) (n k : Nat) (f : Nat → Nat) : Prop where
  strictMono : StrictMono f
  marker_zero : f 0 = 0
  marker_one : f 1 = 1
  marker_two : f 2 = 2
  image_bound : ∀ u : Nat, u < n → f u < k
  role_iff :
    ∀ u : Nat, 3 ≤ u → u < n →
      (IsLeaf T (f u) ↔ IsLeaf A u) ∧
      (IsOneSplit T (f u) ↔ IsOneSplit A u) ∧
      (IsTwoSplit T (f u) ↔ IsTwoSplit A u)
  leaf_edge_iff :
    ∀ a b c : Nat, a < b → b < c → c < n →
      IsLeaf A a → IsLeaf A b → IsLeaf A c →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c)
  leaf_oneMeet :
    ∀ a b : Nat, 3 ≤ a → a < n → 3 ≤ b → b < n →
      IsLeaf A a → IsLeaf A b →
      T.oneMeetLevel (f a) (f b) =
        f (A.oneMeetLevel a b)
  leaf_twoMeet :
    ∀ a b c d : Nat, a < b → c < d →
      3 ≤ a → a < n → 3 ≤ b → b < n →
      3 ≤ c → c < n → 3 ≤ d → d < n →
      IsLeaf A a → IsLeaf A b →
      IsLeaf A c → IsLeaf A d →
      T.twoMeetLevel (f a) (f b) (f c) (f d) =
        f (A.twoMeetLevel a b c d)

/-- Nonmarker source vertices of a true marker-fixing embedding
are also nonmarkers at their target images. -/
theorem FiniteMeetEmbedding.nonmarker_image_ge_three
    {A B : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}
    (E : FiniteMeetEmbedding A B n f)
    (u : Nat) (hu : 3 ≤ u) : 3 ≤ f u := by
  have h2 : f 2 < f u :=
    E.strictMono (by omega : 2 < u)
  rw [E.marker_two] at h2
  omega

/-- A genuine finite diary embedding remains a genuine LEAF
pre-embedding after an arbitrary flip of its target. This
requires only that its prescribed finite image lies inside
the target frame, as is true of the verified JEP construction. -/
theorem FiniteMeetEmbedding.leafPreembedding_after_target_flip
    {A B B' : Ordered3Graph Nat}
    {n k : Nat} {f : Nat → Nat}
    (E : FiniteMeetEmbedding A B n f)
    (hRange : ∀ u : Nat, u < n → f u < k)
    (F : FiniteDiaryFlip B B' k) :
    FiniteLeafPreembedding A B' n k f := by
  refine {
    strictMono := E.strictMono
    marker_zero := E.marker_zero
    marker_one := E.marker_one
    marker_two := E.marker_two
    image_bound := hRange
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u hu3 hu
    have hfu3 : 3 ≤ f u := E.nonmarker_image_ge_three u hu3
    obtain ⟨hLeaf,hOne,hTwo⟩ :=
      F.role_iff (f u) hfu3 (hRange u hu)
    exact ⟨hLeaf.symm.trans (E.leaf_iff u hu3 hu),
      hOne.symm.trans (E.oneSplit_iff u hu3 hu),
      hTwo.symm.trans (E.twoSplit_iff u hu3 hu)⟩
  · intro a b c hab hbc hc ha hb hcLeaf
    have han : a < n := by omega
    have hbn : b < n := by omega
    have hBA : IsLeaf B (f a) :=
      (E.leaf_iff a ha.1 han).mpr ha
    have hBB : IsLeaf B (f b) :=
      (E.leaf_iff b hb.1 hbn).mpr hb
    have hBC : IsLeaf B (f c) :=
      (E.leaf_iff c hcLeaf.1 hc).mpr hcLeaf
    have habImage : f a < f b := E.strictMono hab
    have hbcImage : f b < f c := E.strictMono hbc
    calc
      B'.edge (f a) (f b) (f c) ↔
          B.edge (f a) (f b) (f c) :=
        (F.leaf_edge_iff (f a) (f b) (f c)
          habImage hbcImage (hRange c hc) hBA hBB hBC).symm
      _ ↔ A.edge a b c := E.edge_iff a b c hab hbc hc
  · intro a b ha3 han hb3 hbn ha hb
    have hBA : IsLeaf B (f a) :=
      (E.leaf_iff a ha3 han).mpr ha
    have hBB : IsLeaf B (f b) :=
      (E.leaf_iff b hb3 hbn).mpr hb
    calc
      B'.oneMeetLevel (f a) (f b) =
          B.oneMeetLevel (f a) (f b) :=
        (F.leaf_oneMeet (f a) (f b)
          (hRange a han) (hRange b hbn) hBA hBB).symm
      _ = f (A.oneMeetLevel a b) :=
        E.oneMeet a b ha3 han hb3 hbn
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
      ha hb hc hd
    have hBA : IsLeaf B (f a) :=
      (E.leaf_iff a ha3 han).mpr ha
    have hBB : IsLeaf B (f b) :=
      (E.leaf_iff b hb3 hbn).mpr hb
    have hBC : IsLeaf B (f c) :=
      (E.leaf_iff c hc3 hcn).mpr hc
    have hBD : IsLeaf B (f d) :=
      (E.leaf_iff d hd3 hdn).mpr hd
    calc
      B'.twoMeetLevel (f a) (f b) (f c) (f d) =
          B.twoMeetLevel (f a) (f b) (f c) (f d) :=
        (F.leaf_twoMeet (f a) (f b) (f c) (f d)
          (E.strictMono hab) (E.strictMono hcd)
          (hRange b hbn) (hRange d hdn)
          hBA hBB hBC hBD).symm
      _ = f (A.twoMeetLevel a b c d) :=
        E.twoMeet a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn

end DiaryLeafPriority
end ThreeUniformDiaries
