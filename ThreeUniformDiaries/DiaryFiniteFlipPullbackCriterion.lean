import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection

/-!
# A precise conditional pullback criterion for target diary flips

Let an exact finite diary embedding A -> B use the vertex map f.
Flip the target B to B'. If the induced copy on the SAME vertex map
can be realised as another genuine finite diary P with an exact
finite meet embedding P -> B', then P must be a FLIP OF A.

The proof uses the identity of all leaf-induced triples and
numerical singleton/full ordered-pair meets of leaves between
B and B'. Injectivity of f identifies source meet levels.

This is a conditional algebraic bridge, not a claim that such
a P or its exact mixed-meet embedding always exists. Existence
is the remaining geometric pullback problem, followed by the
separate strict-causality problem for compatible choices.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A P B B' : Ordered3Graph Nat}
variable {n k : Nat} {f : Nat → Nat}

/-- If the same source map f is a protected embedding of A in B
and of P in a flip B' of B, then P is a genuine diary flip of A.
The theorem requires explicitly provided exact embeddings
and therefore does not invent the missing pullback diary. -/
theorem finiteFlip_of_commonMeetEmbedding
    (DA : FiniteRoleDiaryBlock A n)
    (DP : FiniteRoleDiaryBlock P n)
    (E : FiniteMeetEmbedding A B n f)
    (EP : FiniteMeetEmbedding P B' n f)
    (hRange : ∀ u : Nat, u < n → f u < k)
    (F : FiniteDiaryFlip B B' k) :
    FiniteDiaryFlip A P n := by
  have hImage3 (u : Nat) (hu3 : 3 ≤ u) : 3 ≤ f u := by
    have h2 : f 2 < f u := E.strictMono (by omega : 2 < u)
    rw [E.marker_two] at h2
    omega
  have hRoles (u : Nat) (hu3 : 3 ≤ u) (hun : u < n) :
      (IsLeaf A u ↔ IsLeaf P u) ∧
      (IsOneSplit A u ↔ IsOneSplit P u) ∧
      (IsTwoSplit A u ↔ IsTwoSplit P u) := by
    obtain ⟨hLeaf,hOne,hTwo⟩ :=
      F.role_iff (f u) (hImage3 u hu3) (hRange u hun)
    exact ⟨
      (E.leaf_iff u hu3 hun).symm.trans
        (hLeaf.trans (EP.leaf_iff u hu3 hun)),
      (E.oneSplit_iff u hu3 hun).symm.trans
        (hOne.trans (EP.oneSplit_iff u hu3 hun)),
      (E.twoSplit_iff u hu3 hun).symm.trans
        (hTwo.trans (EP.twoSplit_iff u hu3 hun))⟩
  refine {
    source_diary := DA
    target_diary := DP
    role_iff := hRoles
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro a b c hab hbc hcn ha hb hc
    have han : a < n := by omega
    have hbn : b < n := by omega
    have hBA : IsLeaf B (f a) :=
      (E.leaf_iff a ha.1 han).mpr ha
    have hBB : IsLeaf B (f b) :=
      (E.leaf_iff b hb.1 hbn).mpr hb
    have hBC : IsLeaf B (f c) :=
      (E.leaf_iff c hc.1 hcn).mpr hc
    calc
      A.edge a b c ↔ B.edge (f a) (f b) (f c) :=
        (E.edge_iff a b c hab hbc hcn).symm
      _ ↔ B'.edge (f a) (f b) (f c) :=
        F.leaf_edge_iff (f a) (f b) (f c)
          (E.strictMono hab) (E.strictMono hbc)
          (hRange c hcn) hBA hBB hBC
      _ ↔ P.edge a b c := EP.edge_iff a b c hab hbc hcn
  · intro a b han hbn ha hb
    have hBA : IsLeaf B (f a) :=
      (E.leaf_iff a ha.1 han).mpr ha
    have hBB : IsLeaf B (f b) :=
      (E.leaf_iff b hb.1 hbn).mpr hb
    have hPA : IsLeaf P a := (hRoles a ha.1 han).1.mp ha
    have hPB : IsLeaf P b := (hRoles b hb.1 hbn).1.mp hb
    have hOld : B.oneMeetLevel (f a) (f b) =
        f (A.oneMeetLevel a b) :=
      E.oneMeet a b ha.1 han hb.1 hbn
    have hTarget : B'.oneMeetLevel (f a) (f b) =
        f (P.oneMeetLevel a b) :=
      EP.oneMeet a b hPA.1 han hPB.1 hbn
    have hFlip := F.leaf_oneMeet (f a) (f b)
      (hRange a han) (hRange b hbn) hBA hBB
    have hEq : f (A.oneMeetLevel a b) =
        f (P.oneMeetLevel a b) :=
      hOld.symm.trans (hFlip.trans hTarget)
    exact E.strictMono.injective hEq
  · intro a b c d hab hcd hbn hdn ha hb hc hd
    have han : a < n := by omega
    have hcn : c < n := by omega
    have hBA : IsLeaf B (f a) :=
      (E.leaf_iff a ha.1 han).mpr ha
    have hBB : IsLeaf B (f b) :=
      (E.leaf_iff b hb.1 hbn).mpr hb
    have hBC : IsLeaf B (f c) :=
      (E.leaf_iff c hc.1 hcn).mpr hc
    have hBD : IsLeaf B (f d) :=
      (E.leaf_iff d hd.1 hdn).mpr hd
    have hPA : IsLeaf P a := (hRoles a ha.1 han).1.mp ha
    have hPB : IsLeaf P b := (hRoles b hb.1 hbn).1.mp hb
    have hPC : IsLeaf P c := (hRoles c hc.1 hcn).1.mp hc
    have hPD : IsLeaf P d := (hRoles d hd.1 hdn).1.mp hd
    have hOld : B.twoMeetLevel (f a) (f b) (f c) (f d) =
        f (A.twoMeetLevel a b c d) :=
      E.twoMeet a b c d hab hcd
        ha.1 han hb.1 hbn hc.1 hcn hd.1 hdn
    have hTarget : B'.twoMeetLevel (f a) (f b) (f c) (f d) =
        f (P.twoMeetLevel a b c d) :=
      EP.twoMeet a b c d hab hcd
        hPA.1 han hPB.1 hbn hPC.1 hcn hPD.1 hdn
    have hFlip := F.leaf_twoMeet (f a) (f b) (f c) (f d)
      (E.strictMono hab) (E.strictMono hcd)
      (hRange b hbn) (hRange d hdn) hBA hBB hBC hBD
    have hEq : f (A.twoMeetLevel a b c d) =
        f (P.twoMeetLevel a b c d) :=
      hOld.symm.trans (hFlip.trans hTarget)
    exact E.strictMono.injective hEq

end DiaryLeafPriority
end ThreeUniformDiaries
