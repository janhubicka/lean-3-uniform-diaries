import ThreeUniformDiaries.DiaryCofinalFullPrefixCompression
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Full retained prefixes preserve exact capped type meets

If two ternary ordered graphs agree on all increasing triples inside
[0,b), then all singleton and full two-type meets of points in that
prefix agree LITERALLY, provided the compared two-type arguments are
increasing pairs.

This is not a general theorem about nonconvex embeddings. It works
because the whole old testing interval is present: every triple that
could distinguish types below the capped meet occurs in [0,b).
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

private theorem oneTypeBelow_iff_of_prefix
    (G K : Ordered3Graph Nat) (b l u v : Nat)
    (hu : u < b) (hv : v < b) (hl : l ≤ min u v)
    (hEdge : ∀ x y z : Nat, x < y → y < z → z < b →
      (G.edge x y z ↔ K.edge x y z)) :
    G.SameOneTypeBelow l u v ↔ K.SameOneTypeBelow l u v := by
  have hlu : l ≤ u := hl.trans (min_le_left _ _)
  have hlv : l ≤ v := hl.trans (min_le_right _ _)
  constructor
  · intro h x y hxy hyl
    have hyu : y < u := lt_of_lt_of_le hyl hlu
    have hyv : y < v := lt_of_lt_of_le hyl hlv
    calc
      K.edge x y u ↔ G.edge x y u := (hEdge x y u hxy hyu hu).symm
      _ ↔ G.edge x y v := h hxy hyl
      _ ↔ K.edge x y v := hEdge x y v hxy hyv hv
  · intro h x y hxy hyl
    have hyu : y < u := lt_of_lt_of_le hyl hlu
    have hyv : y < v := lt_of_lt_of_le hyl hlv
    calc
      G.edge x y u ↔ K.edge x y u := hEdge x y u hxy hyu hu
      _ ↔ K.edge x y v := h hxy hyl
      _ ↔ G.edge x y v := (hEdge x y v hxy hyv hv).symm

private theorem auxTypeBelow_iff_of_prefix
    (G K : Ordered3Graph Nat) (b l u₀ u₁ v₀ v₁ : Nat)
    (hu : u₀ < u₁) (hv : v₀ < v₁)
    (hu₁ : u₁ < b) (hv₁ : v₁ < b)
    (hl : l ≤ min u₀ v₀)
    (hEdge : ∀ x y z : Nat, x < y → y < z → z < b →
      (G.edge x y z ↔ K.edge x y z)) :
    G.SameAuxTypeBelow l u₀ u₁ v₀ v₁ ↔
      K.SameAuxTypeBelow l u₀ u₁ v₀ v₁ := by
  have hlu : l ≤ u₀ := hl.trans (min_le_left _ _)
  have hlv : l ≤ v₀ := hl.trans (min_le_right _ _)
  constructor
  · intro h x hx
    have hxu : x < u₀ := lt_of_lt_of_le hx hlu
    have hxv : x < v₀ := lt_of_lt_of_le hx hlv
    calc
      K.edge x u₀ u₁ ↔ G.edge x u₀ u₁ :=
        (hEdge x u₀ u₁ hxu hu hu₁).symm
      _ ↔ G.edge x v₀ v₁ := h hx
      _ ↔ K.edge x v₀ v₁ := hEdge x v₀ v₁ hxv hv hv₁
  · intro h x hx
    have hxu : x < u₀ := lt_of_lt_of_le hx hlu
    have hxv : x < v₀ := lt_of_lt_of_le hx hlv
    calc
      G.edge x u₀ u₁ ↔ K.edge x u₀ u₁ :=
        hEdge x u₀ u₁ hxu hu hu₁
      _ ↔ K.edge x v₀ v₁ := h hx
      _ ↔ G.edge x v₀ v₁ := (hEdge x v₀ v₁ hxv hv hv₁).symm

private theorem twoTypeBelow_iff_of_prefix
    (G K : Ordered3Graph Nat) (b l u₀ u₁ v₀ v₁ : Nat)
    (hu : u₀ < u₁) (hv : v₀ < v₁)
    (hu₁ : u₁ < b) (hv₁ : v₁ < b)
    (hl : l ≤ min u₀ v₀)
    (hEdge : ∀ x y z : Nat, x < y → y < z → z < b →
      (G.edge x y z ↔ K.edge x y z)) :
    G.SameTwoTypeBelow l u₀ u₁ v₀ v₁ ↔
      K.SameTwoTypeBelow l u₀ u₁ v₀ v₁ := by
  have hU0 : u₀ < b := lt_trans hu hu₁
  have hV0 : v₀ < b := lt_trans hv hv₁
  have hSecond : l ≤ min u₁ v₁ := by
    apply le_min
    · exact (hl.trans (min_le_left _ _)).trans hu.le
    · exact (hl.trans (min_le_right _ _)).trans hv.le
  exact and_congr
    (oneTypeBelow_iff_of_prefix G K b l u₀ v₀ hU0 hV0 hl hEdge)
    (and_congr
      (oneTypeBelow_iff_of_prefix G K b l u₁ v₁ hu₁ hv₁ hSecond hEdge)
      (auxTypeBelow_iff_of_prefix G K b l u₀ u₁ v₀ v₁
        hu hv hu₁ hv₁ hl hEdge))

/-- Exact singleton meet agreement on any completely retained
bounded prefix. -/
theorem oneMeetLevel_eq_of_prefix
    (G K : Ordered3Graph Nat) (b u v : Nat)
    (hu : u < b) (hv : v < b)
    (hEdge : ∀ x y z : Nat, x < y → y < z → z < b →
      (G.edge x y z ↔ K.edge x y z)) :
    G.oneMeetLevel u v = K.oneMeetLevel u v := by
  classical
  have hG : G.oneMeetLevel u v ≤ min u v :=
    G.oneMeetLevel_le_min u v
  have hK : K.oneMeetLevel u v ≤ min u v :=
    K.oneMeetLevel_le_min u v
  have hGK : G.oneMeetLevel u v ≤ K.oneMeetLevel u v := by
    apply Nat.le_findGreatest hG
    exact (oneTypeBelow_iff_of_prefix G K b
      (G.oneMeetLevel u v) u v hu hv hG hEdge).mp
      (G.oneMeetLevel_agree u v)
  have hKG : K.oneMeetLevel u v ≤ G.oneMeetLevel u v := by
    apply Nat.le_findGreatest hK
    exact (oneTypeBelow_iff_of_prefix G K b
      (K.oneMeetLevel u v) u v hu hv hK hEdge).mpr
      (K.oneMeetLevel_agree u v)
  omega

/-- Exact full two-type meet agreement on two increasing pairs
in any completely retained bounded prefix. -/
theorem twoMeetLevel_eq_of_prefix
    (G K : Ordered3Graph Nat)
    (b u₀ u₁ v₀ v₁ : Nat)
    (hu : u₀ < u₁) (hv : v₀ < v₁)
    (hu₁ : u₁ < b) (hv₁ : v₁ < b)
    (hEdge : ∀ x y z : Nat, x < y → y < z → z < b →
      (G.edge x y z ↔ K.edge x y z)) :
    G.twoMeetLevel u₀ u₁ v₀ v₁ =
      K.twoMeetLevel u₀ u₁ v₀ v₁ := by
  classical
  have hG : G.twoMeetLevel u₀ u₁ v₀ v₁ ≤ min u₀ v₀ :=
    G.twoMeetLevel_le_min u₀ u₁ v₀ v₁
  have hK : K.twoMeetLevel u₀ u₁ v₀ v₁ ≤ min u₀ v₀ :=
    K.twoMeetLevel_le_min u₀ u₁ v₀ v₁
  have hGK : G.twoMeetLevel u₀ u₁ v₀ v₁ ≤
      K.twoMeetLevel u₀ u₁ v₀ v₁ := by
    apply Nat.le_findGreatest hG
    exact (twoTypeBelow_iff_of_prefix G K b
      (G.twoMeetLevel u₀ u₁ v₀ v₁) u₀ u₁ v₀ v₁
      hu hv hu₁ hv₁ hG hEdge).mp
      (G.twoMeetLevel_agree u₀ u₁ v₀ v₁)
  have hKG : K.twoMeetLevel u₀ u₁ v₀ v₁ ≤
      G.twoMeetLevel u₀ u₁ v₀ v₁ := by
    apply Nat.le_findGreatest hK
    exact (twoTypeBelow_iff_of_prefix G K b
      (K.twoMeetLevel u₀ u₁ v₀ v₁) u₀ u₁ v₀ v₁
      hu hv hu₁ hv₁ hK hEdge).mpr
      (K.twoMeetLevel_agree u₀ u₁ v₀ v₁)
  omega

/-- Apply the generic prefix lemma to a finite support containing
[0,b), whose indices are unchanged on that interval. -/
theorem finiteSupportGraph_oneMeet_prefix_eq
    (G : Ordered3Graph Nat) (S : Finset Nat) (b u v : Nat)
    (hPrefix : Finset.range b ⊆ S)
    (hu : u < b) (hv : v < b) :
    (finiteSupportGraph G S).oneMeetLevel u v =
      G.oneMeetLevel u v := by
  apply oneMeetLevel_eq_of_prefix
    (finiteSupportGraph G S) G b u v hu hv
  intro x y z hxy hyz hzb
  exact finiteSupportGraph_edge_prefix_iff
    G S b hPrefix x y z hxy hyz hzb

/-- The corresponding full ordered-pair meet is also unchanged
below a retained prefix. -/
theorem finiteSupportGraph_twoMeet_prefix_eq
    (G : Ordered3Graph Nat) (S : Finset Nat)
    (b u₀ u₁ v₀ v₁ : Nat)
    (hPrefix : Finset.range b ⊆ S)
    (hu : u₀ < u₁) (hv : v₀ < v₁)
    (hu₁ : u₁ < b) (hv₁ : v₁ < b) :
    (finiteSupportGraph G S).twoMeetLevel u₀ u₁ v₀ v₁ =
      G.twoMeetLevel u₀ u₁ v₀ v₁ := by
  apply twoMeetLevel_eq_of_prefix
    (finiteSupportGraph G S) G b u₀ u₁ v₀ v₁
      hu hv hu₁ hv₁
  intro x y z hxy hyz hzb
  exact finiteSupportGraph_edge_prefix_iff
    G S b hPrefix x y z hxy hyz hzb

end DiaryLeafPriority
end ThreeUniformDiaries
