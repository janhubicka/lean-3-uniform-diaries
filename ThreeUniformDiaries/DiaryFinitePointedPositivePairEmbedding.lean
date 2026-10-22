import ThreeUniformDiaries.DiaryFiniteExplicitSmallTargetDiary
import ThreeUniformDiaries.DiaryFinitePullbackProtectedEmbedding
import ThreeUniformDiaries.DiaryFiniteThreeLeafAlternation

/-!
# A positive ordered one-split pair contains the small source diary

Given any finite diary T, an actual one-split s and two leaves
s < p < q whose exact singleton meet is s, with the earlier leaf
negative and later leaf positive at s, there is a bounded fully
meet-preserving embedding of the concrete six-vertex source
smallFlipSource into T.

The map fixes the markers and sends 3 -> s, 4 -> p, 5 -> q.
Its infinite tail is only a bookkeeping extension. The source
is a genuine finite diary (#838), and the target is an arbitrary
genuine finite diary. The proof must establish inducedness on all
edges AND nonedges and the exact leaf meet data; then the verified
finite induced leaf-preembedding interface transports all mixed
meets. No target rigidity or independent split controls are used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Extend the pointed map from the source's three markers, one
split, and two leaves to an increasing total map on Nat. -/
def smallPointedPairMap (s p q u : Nat) : Nat :=
  if u < 3 then u
  else if u = 3 then s
  else if u = 4 then p
  else q + (u - 5)

theorem smallPointedPairMap_strictMono
    (s p q : Nat) (hs : 3 ≤ s) (hsp : s < p) (hpq : p < q) :
    StrictMono (smallPointedPairMap s p q) := by
  intro a b hab
  unfold smallPointedPairMap
  split_ifs <;> omega

theorem smallPointedPairMap_marker_zero (s p q : Nat) :
    smallPointedPairMap s p q 0 = 0 := by
  simp [smallPointedPairMap]
theorem smallPointedPairMap_marker_one (s p q : Nat) :
    smallPointedPairMap s p q 1 = 1 := by
  simp [smallPointedPairMap]
theorem smallPointedPairMap_marker_two (s p q : Nat) :
    smallPointedPairMap s p q 2 = 2 := by
  simp [smallPointedPairMap]
theorem smallPointedPairMap_split (s p q : Nat) :
    smallPointedPairMap s p q 3 = s := by
  simp [smallPointedPairMap]
theorem smallPointedPairMap_leaf0 (s p q : Nat) :
    smallPointedPairMap s p q 4 = p := by
  simp [smallPointedPairMap]
theorem smallPointedPairMap_leaf1 (s p q : Nat) :
    smallPointedPairMap s p q 5 = q := by
  simp [smallPointedPairMap]

/-- The arbitrary tail of the map is harmless; its actual
six source vertices land strictly within the finite target. -/
theorem smallPointedPairMap_bounded
    (s p q k : Nat) (hs : 3 ≤ s) (hsp : s < p)
    (hpq : p < q) (hqk : q < k) :
    ∀ u : Nat, u < 6 → smallPointedPairMap s p q u < k := by
  intro u hu
  have hcase : u=0 ∨ u=1 ∨ u=2 ∨ u=3 ∨ u=4 ∨ u=5 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [smallPointedPairMap] <;> omega

/-- An oriented genuine pair at a one-split is a full protected
copy of the basic six-vertex diary, not merely an induced edge
pattern on its leaves. -/
theorem smallFlipSource_embeds_of_positive_oneSplit
    {T : Ordered3Graph Nat} {k : Nat}
    (D : FiniteRoleDiaryBlock T k)
    (s p q : Nat)
    (hs : IsOneSplit T s) (hsp : s < p)
    (hpq : p < q) (hqk : q < k)
    (hp : IsLeaf T p) (hq : IsLeaf T q)
    (hMeet : T.oneMeetLevel p q = s)
    (hNegative : ¬ T.edge 0 s p)
    (hPositive : T.edge 0 s q) :
    ∃ f : Nat → Nat, FiniteBoundedMeetEmbedding
      smallFlipSource T 6 k f := by
  classical
  let f := smallPointedPairMap s p q
  have hMono : StrictMono f :=
    smallPointedPairMap_strictMono s p q hs.1 hsp hpq
  have hBound : ∀ u : Nat, u < 6 → f u < k :=
    smallPointedPairMap_bounded s p q k hs.1 hsp hpq hqk
  have hLex : LexEarlier T p q :=
    (E_oneSplit_lexEarlier_iff_right
      D.prediary.permitted_edge s p q hs hpq hsp hMeet).mpr
        hPositive
  have hMarkerOne : T.edge 1 p q :=
    (D.prediary.leaf_marker_one p q hpq hqk hp hq).mpr hLex
  have hMarkerTwo : ¬ T.edge 2 p q := by
    intro he
    exact ((D.prediary.leaf_marker_two p q hpq hqk hp hq).mp he)
      hLex
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
        (T.edge (f a) (f b) (f c) ↔ smallFlipSource.edge a b c) := by
    intro a b c hab hbc hc6
    have ha6 : a < 6 := by omega
    have hb6 : b < 6 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      simp_all [f,smallPointedPairMap,smallFlipSource,hs.2.1,hs.2.2,
        hp.2.1,hp.2.2,hq.2.1,hq.2.2]
  have hRole :
      ∀ u : Nat, 3 ≤ u → u < 6 →
       (IsLeaf T (f u) ↔ IsLeaf smallFlipSource u) ∧
       (IsOneSplit T (f u) ↔ IsOneSplit smallFlipSource u) ∧
       (IsTwoSplit T (f u) ↔ IsTwoSplit smallFlipSource u) := by
    intro u hu3 hu6
    have hCase : u=3 ∨ u=4 ∨ u=5 := by omega
    rcases hCase with rfl | rfl | rfl <;>
      simp [f,smallPointedPairMap,IsLeaf,IsOneSplit,IsTwoSplit,
        smallFlipSource,hs.1,hs.2.1,hs.2.2,
        hp.1,hp.2.1,hp.2.2,hq.1,hq.2.1,hq.2.2]
  have hLeafMeet :
      ∀ a b : Nat, 3 ≤ a → a < 6 → 3 ≤ b → b < 6 →
      IsLeaf smallFlipSource a → IsLeaf smallFlipSource b →
      T.oneMeetLevel (f a) (f b) =
        f (smallFlipSource.oneMeetLevel a b) := by
    intro a b ha3 ha6 hb3 hb6 haLeaf hbLeaf
    have haCases := (smallFlipSource_leaf_iff a ha3 ha6).mp haLeaf
    have hbCases := (smallFlipSource_leaf_iff b hb3 hb6).mp hbLeaf
    rcases haCases with rfl | rfl <;> rcases hbCases with rfl | rfl
    · simp [f,smallPointedPairMap,Ordered3Graph.oneMeetLevel_self_eq]
    · change T.oneMeetLevel p q = s
      exact hMeet
    · have hTargetReverse := finiteLeafMeet_oneMeet_comm T q p
      have hSourceReverse := finiteLeafMeet_oneMeet_comm
        smallFlipSource 5 4
      calc
        T.oneMeetLevel (f 5) (f 4) =
            T.oneMeetLevel q p := by simp [f,smallPointedPairMap]
        _ = T.oneMeetLevel p q := hTargetReverse
        _ = s := hMeet
        _ = f (smallFlipSource.oneMeetLevel 5 4) := by
          rw [hSourceReverse,smallFlipSource_leaf_meet]
          simp [f,smallPointedPairMap]
    · simp [f,smallPointedPairMap,Ordered3Graph.oneMeetLevel_self_eq]
  have hLeafTwoMeet :
      ∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → a < 6 → 3 ≤ b → b < 6 →
        3 ≤ c → c < 6 → 3 ≤ d → d < 6 →
        IsLeaf smallFlipSource a → IsLeaf smallFlipSource b →
        IsLeaf smallFlipSource c → IsLeaf smallFlipSource d →
        T.twoMeetLevel (f a) (f b) (f c) (f d) =
          f (smallFlipSource.twoMeetLevel a b c d) := by
    intro a b c d hab hcd ha3 ha6 hb3 hb6 hc3 hc6 hd3 hd6
      haLeaf hbLeaf hcLeaf hdLeaf
    have haC := (smallFlipSource_leaf_iff a ha3 ha6).mp haLeaf
    have hbC := (smallFlipSource_leaf_iff b hb3 hb6).mp hbLeaf
    have hcC := (smallFlipSource_leaf_iff c hc3 hc6).mp hcLeaf
    have hdC := (smallFlipSource_leaf_iff d hd3 hd6).mp hdLeaf
    have haa : a=4 := by omega
    have hbb : b=5 := by omega
    have hcc : c=4 := by omega
    have hdd : d=5 := by omega
    subst a; subst b; subst c; subst d
    change T.twoMeetLevel p q p q =
      smallPointedPairMap s p q
        (smallFlipSource.twoMeetLevel 4 5 4 5)
    rw [Ordered3Graph.twoMeetLevel_self_eq T p q hpq,
      Ordered3Graph.twoMeetLevel_self_eq smallFlipSource 4 5 (by omega)]
    simp [smallPointedPairMap]
  have Q : FiniteLeafPreembedding smallFlipSource T 6 k f := {
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
      have hAc := (smallFlipSource_leaf_iff a ha.1 ha6).mp ha
      have hBc := (smallFlipSource_leaf_iff b hb.1 hb6).mp hb
      omega
    leaf_oneMeet := hLeafMeet
    leaf_twoMeet := hLeafTwoMeet
  }
  refine ⟨f, ?_⟩
  exact ⟨Q.toMeetEmbedding_of_induced
    smallFlipSource_is_finiteDiary.prediary D.prediary
    hInduced,hBound⟩

end DiaryLeafPriority
end ThreeUniformDiaries
