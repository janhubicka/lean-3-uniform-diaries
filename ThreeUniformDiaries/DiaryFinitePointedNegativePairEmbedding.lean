import ThreeUniformDiaries.DiaryFinitePointedPositivePairEmbedding
import ThreeUniformDiaries.DiaryFiniteExplicitOppositeSmallSource

/-!
# Negative-right one-split orientation embeds the opposite six-vertex source

A genuine pair of ordered leaves p<q with meet s and E2 branch
incidences (0,s,p)=true, (0,s,q)=false has the marker-two orientation
and induces a protected, bounded copy of smallFlipSourceOpposite.

The proof parallels the positive-right source case but proves all
induced edges and nonedges and all numerical mixed meets by the
finite leaf-preembedding interface. The target is any genuine
bounded finite diary. No arbitrary bit flips are admitted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

theorem smallFlipSourceOpposite_embeds_of_negative_oneSplit
    {T : Ordered3Graph Nat} {k : Nat}
    (D : FiniteRoleDiaryBlock T k)
    (s p q : Nat)
    (hs : IsOneSplit T s) (hsp : s < p)
    (hpq : p < q) (hqk : q < k)
    (hp : IsLeaf T p) (hq : IsLeaf T q)
    (hMeet : T.oneMeetLevel p q = s)
    (hPositive : T.edge 0 s p)
    (hNegative : ¬ T.edge 0 s q) :
    ∃ f : Nat → Nat, FiniteBoundedMeetEmbedding
      smallFlipSourceOpposite T 6 k f := by
  classical
  let f := smallPointedPairMap s p q
  have hMono : StrictMono f :=
    smallPointedPairMap_strictMono s p q hs.1 hsp hpq
  have hBound : ∀ u : Nat, u < 6 → f u < k :=
    smallPointedPairMap_bounded s p q k hs.1 hsp hpq hqk
  have hNotLex : ¬ LexEarlier T p q := by
    intro hLex
    exact hNegative
      ((E_oneSplit_lexEarlier_iff_right
        D.prediary.permitted_edge s p q hs hpq hsp hMeet).mp hLex)
  have hMarkerOne : ¬ T.edge 1 p q := by
    intro he
    exact hNotLex
      ((D.prediary.leaf_marker_one p q hpq hqk hp hq).mp he)
  have hMarkerTwo : T.edge 2 p q :=
    (D.prediary.leaf_marker_two p q hpq hqk hp hq).mpr hNotLex
  have hNoLeafS : ¬ IsLeaf T s := by
    intro h
    exact h.2.1 hs.2.1
  have hNoTwoS : ¬ IsTwoSplit T s := by
    intro h
    exact h.2.1 hs.2.1
  have hNoOneP : ¬ IsOneSplit T p := by
    intro h
    exact hp.2.1 h.2.1
  have hNoTwoP : ¬ IsTwoSplit T p := by
    intro h
    exact hp.2.2 h.2.2
  have hNoOneQ : ¬ IsOneSplit T q := by
    intro h
    exact hq.2.1 h.2.1
  have hNoTwoQ : ¬ IsTwoSplit T q := by
    intro h
    exact hq.2.2 h.2.2
  have hs3 : 3 ≤ s := hs.1
  have hp3 : 3 ≤ p := hp.1
  have hq3 : 3 ≤ q := hq.1
  have hNo012 : ¬ T.edge 0 1 2 := by
    intro he
    have hh := D.prediary.frame.edge_support 0 1 2 he
    omega
  have hNo12 (w : Nat) : ¬ T.edge 1 2 w := by
    intro he
    rcases D.prediary.permitted_edge 1 2 w he with
        h1 | h2 | h3 | h4 | h5
    · omega
    · omega
    · have hh : 3 ≤ (1:Nat) := h3.1.1
      omega
    · have hh : 3 ≤ (2:Nat) := h4.2.1.1
      omega
    · have hh : 3 ≤ (1:Nat) := h5.1.1
      omega
  have hNo0pq : ¬ T.edge 0 p q := by
    intro he
    rcases D.prediary.permitted_edge 0 p q he with
        h1 | h2 | h3 | h4 | h5
    · omega
    · exact hNoOneP h2.2.1
    · have hh : 3 ≤ (0:Nat) := h3.1.1
      omega
    · omega
    · have hh : 3 ≤ (0:Nat) := h5.1.1
      omega
  have hNoSpq : ¬ T.edge s p q := by
    intro he
    rcases D.prediary.permitted_edge s p q he with
        h1 | h2 | h3 | h4 | h5
    · omega
    · omega
    · exact hNoTwoS h3.1
    · omega
    · exact hNoLeafS h5.1
  have hNo1sp : ¬ T.edge 1 s p :=
    E_oneSplit_no_positive_aux D.prediary.permitted_edge
      s 1 p hs (by omega)
  have hNo1sq : ¬ T.edge 1 s q :=
    E_oneSplit_no_positive_aux D.prediary.permitted_edge
      s 1 q hs (by omega)
  have hNo2sp : ¬ T.edge 2 s p :=
    E_oneSplit_no_positive_aux D.prediary.permitted_edge
      s 2 p hs (by omega)
  have hNo2sq : ¬ T.edge 2 s q :=
    E_oneSplit_no_positive_aux D.prediary.permitted_edge
      s 2 q hs (by omega)
  have hInduced :
      ∀ a b c : Nat, a < b → b < c → c < 6 →
        (T.edge (f a) (f b) (f c) ↔ smallFlipSourceOpposite.edge a b c) := by
    intro a b c hab hbc hc6
    have ha6 : a < 6 := by omega
    have hb6 : b < 6 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      simp_all [f,smallPointedPairMap,smallFlipSourceOpposite,hs.2.1,hs.2.2,
        hp.2.1,hp.2.2,hq.2.1,hq.2.2]
  have hRole :
      ∀ u : Nat, 3 ≤ u → u < 6 →
       (IsLeaf T (f u) ↔ IsLeaf smallFlipSourceOpposite u) ∧
       (IsOneSplit T (f u) ↔ IsOneSplit smallFlipSourceOpposite u) ∧
       (IsTwoSplit T (f u) ↔ IsTwoSplit smallFlipSourceOpposite u) := by
    intro u hu3 hu6
    have hCase : u=3 ∨ u=4 ∨ u=5 := by omega
    rcases hCase with rfl | rfl | rfl <;>
      simp [f,smallPointedPairMap,IsLeaf,IsOneSplit,IsTwoSplit,
        smallFlipSourceOpposite,hs.1,hs.2.1,hs.2.2,
        hp.1,hp.2.1,hp.2.2,hq.1,hq.2.1,hq.2.2]
  have hLeafMeet :
      ∀ a b : Nat, 3 ≤ a → a < 6 → 3 ≤ b → b < 6 →
      IsLeaf smallFlipSourceOpposite a → IsLeaf smallFlipSourceOpposite b →
      T.oneMeetLevel (f a) (f b) =
        f (smallFlipSourceOpposite.oneMeetLevel a b) := by
    intro a b ha3 ha6 hb3 hb6 haLeaf hbLeaf
    have haCases := (smallFlipSourceOpposite_leaf_iff a ha3 ha6).mp haLeaf
    have hbCases := (smallFlipSourceOpposite_leaf_iff b hb3 hb6).mp hbLeaf
    rcases haCases with rfl | rfl <;> rcases hbCases with rfl | rfl
    · simp [f,smallPointedPairMap,Ordered3Graph.oneMeetLevel_self_eq]
    · rw [smallFlipSourceOpposite_leaf_meet]
      simpa [f,smallPointedPairMap] using hMeet
    · have hTargetReverse := finiteLeafMeet_oneMeet_comm T q p
      have hSourceReverse := finiteLeafMeet_oneMeet_comm
        smallFlipSourceOpposite 5 4
      calc
        T.oneMeetLevel (f 5) (f 4) =
            T.oneMeetLevel q p := by simp [f,smallPointedPairMap]
        _ = T.oneMeetLevel p q := hTargetReverse
        _ = s := hMeet
        _ = f (smallFlipSourceOpposite.oneMeetLevel 5 4) := by
          rw [hSourceReverse,smallFlipSourceOpposite_leaf_meet]
          simp [f,smallPointedPairMap]
    · simp [f,smallPointedPairMap,Ordered3Graph.oneMeetLevel_self_eq]
  have hLeafTwoMeet :
      ∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → a < 6 → 3 ≤ b → b < 6 →
        3 ≤ c → c < 6 → 3 ≤ d → d < 6 →
        IsLeaf smallFlipSourceOpposite a → IsLeaf smallFlipSourceOpposite b →
        IsLeaf smallFlipSourceOpposite c → IsLeaf smallFlipSourceOpposite d →
        T.twoMeetLevel (f a) (f b) (f c) (f d) =
          f (smallFlipSourceOpposite.twoMeetLevel a b c d) := by
    intro a b c d hab hcd ha3 ha6 hb3 hb6 hc3 hc6 hd3 hd6
      haLeaf hbLeaf hcLeaf hdLeaf
    have haC := (smallFlipSourceOpposite_leaf_iff a ha3 ha6).mp haLeaf
    have hbC := (smallFlipSourceOpposite_leaf_iff b hb3 hb6).mp hbLeaf
    have hcC := (smallFlipSourceOpposite_leaf_iff c hc3 hc6).mp hcLeaf
    have hdC := (smallFlipSourceOpposite_leaf_iff d hd3 hd6).mp hdLeaf
    have haa : a=4 := by omega
    have hbb : b=5 := by omega
    have hcc : c=4 := by omega
    have hdd : d=5 := by omega
    subst a; subst b; subst c; subst d
    change T.twoMeetLevel p q p q =
      smallPointedPairMap s p q
        (smallFlipSourceOpposite.twoMeetLevel 4 5 4 5)
    rw [Ordered3Graph.twoMeetLevel_self_eq T p q hpq,
      Ordered3Graph.twoMeetLevel_self_eq smallFlipSourceOpposite 4 5 (by omega)]
    simp [smallPointedPairMap]
  have Q : FiniteLeafPreembedding smallFlipSourceOpposite T 6 k f := {
    strictMono := hMono
    marker_zero := smallPointedPairMap_marker_zero s p q
    marker_one := smallPointedPairMap_marker_one s p q
    marker_two := smallPointedPairMap_marker_two s p q
    image_bound := hBound
    role_iff := hRole
    leaf_edge_iff := by
      intro a b c hab hbc hc6 ha hb hc
      have ha6 : a < 6 := by omega
      have hb6 : b < 6 := by omega
      have hAc := (smallFlipSourceOpposite_leaf_iff a ha.1 ha6).mp ha
      have hBc := (smallFlipSourceOpposite_leaf_iff b hb.1 hb6).mp hb
      omega
    leaf_oneMeet := hLeafMeet
    leaf_twoMeet := hLeafTwoMeet
  }
  refine ⟨f, ?_⟩
  exact ⟨Q.toMeetEmbedding_of_induced
    smallFlipSourceOpposite_is_finiteDiary.prediary D.prediary
    hInduced,hBound⟩


end DiaryLeafPriority
end ThreeUniformDiaries
