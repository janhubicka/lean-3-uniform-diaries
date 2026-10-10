import ThreeUniformDiaries.ExactTypeMeetLevels
import ThreeUniformDiaries.InfinitePrefixes
import ThreeUniformDiaries.TypeRepresentation

/-!
# Exact capped meets depend only on the relevant finite prefix

Both capped singleton meets and capped auxiliary meets are determined
solely by increasing edges whose largest index occurs among the
vertices whose types are being compared. Agreement of two infinite
graphs below a finite cut therefore yields exact equality of their
capped meet levels for all selected vertices below the cut.

In particular a graph and any of its finite initial segments have
literally the same capped meets on vertices belonging to that segment.
These lemmas allow us to pass from checked finite canonical-map meet
preservation to a coherent infinite union without assumptions about
what happens at ambient indices above the cut.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The singleton meet of vertices below N is unchanged whenever
two edge predicates agree on all increasing triples below N. -/
theorem oneMeetLevel_eq_of_edge_iff_below
    (H G : Ordered3Graph Nat) {N u v : Nat}
    (hu : u < N) (hv : v < N)
    (he : ∀ a b c : Nat, a < b → b < c → c < N →
      (H.edge a b c ↔ G.edge a b c)) :
    H.oneMeetLevel u v = G.oneMeetLevel u v := by
  classical
  have htypes (w : Nat) (hw : w ≤ min u v) :
      H.SameOneTypeBelow w u v ↔ G.SameOneTypeBelow w u v := by
    have hwu : w ≤ u := hw.trans (min_le_left _ _)
    have hwv : w ≤ v := hw.trans (min_le_right _ _)
    constructor
    · intro hs a b hab hb
      have hbu : b < u := lt_of_lt_of_le hb hwu
      have hbv : b < v := lt_of_lt_of_le hb hwv
      calc
        G.edge a b u ↔ H.edge a b u :=
          (he a b u hab hbu hu).symm
        _ ↔ H.edge a b v := hs hab hb
        _ ↔ G.edge a b v := he a b v hab hbv hv
    · intro hs a b hab hb
      have hbu : b < u := lt_of_lt_of_le hb hwu
      have hbv : b < v := lt_of_lt_of_le hb hwv
      calc
        H.edge a b u ↔ G.edge a b u :=
          he a b u hab hbu hu
        _ ↔ G.edge a b v := hs hab hb
        _ ↔ H.edge a b v := (he a b v hab hbv hv).symm
  have hHG : H.oneMeetLevel u v ≤ G.oneMeetLevel u v :=
    Nat.le_findGreatest (H.oneMeetLevel_le_min u v)
      ((htypes _ (H.oneMeetLevel_le_min u v)).mp
        (H.oneMeetLevel_agree u v))
  have hGH : G.oneMeetLevel u v ≤ H.oneMeetLevel u v :=
    Nat.le_findGreatest (G.oneMeetLevel_le_min u v)
      ((htypes _ (G.oneMeetLevel_le_min u v)).mpr
        (G.oneMeetLevel_agree u v))
  exact Nat.le_antisymm hHG hGH

/-- The same finite-cut invariance for capped auxiliary meets. -/
theorem auxMeetLevel_eq_of_edge_iff_below
    (H G : Ordered3Graph Nat)
    {N u₀ u₁ v₀ v₁ : Nat}
    (hu : u₀ < u₁) (huN : u₁ < N)
    (hv : v₀ < v₁) (hvN : v₁ < N)
    (he : ∀ a b c : Nat, a < b → b < c → c < N →
      (H.edge a b c ↔ G.edge a b c)) :
    H.auxMeetLevel u₀ u₁ v₀ v₁ =
      G.auxMeetLevel u₀ u₁ v₀ v₁ := by
  classical
  have htypes (w : Nat) (hw : w ≤ min u₀ v₀) :
      H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ ↔
        G.SameAuxTypeBelow w u₀ u₁ v₀ v₁ := by
    have hwu : w ≤ u₀ := hw.trans (min_le_left _ _)
    have hwv : w ≤ v₀ := hw.trans (min_le_right _ _)
    constructor
    · intro hs a ha
      have hau : a < u₀ := lt_of_lt_of_le ha hwu
      have hav : a < v₀ := lt_of_lt_of_le ha hwv
      calc
        G.edge a u₀ u₁ ↔ H.edge a u₀ u₁ :=
          (he a u₀ u₁ hau hu huN).symm
        _ ↔ H.edge a v₀ v₁ := hs ha
        _ ↔ G.edge a v₀ v₁ := he a v₀ v₁ hav hv hvN
    · intro hs a ha
      have hau : a < u₀ := lt_of_lt_of_le ha hwu
      have hav : a < v₀ := lt_of_lt_of_le ha hwv
      calc
        H.edge a u₀ u₁ ↔ G.edge a u₀ u₁ :=
          he a u₀ u₁ hau hu huN
        _ ↔ G.edge a v₀ v₁ := hs ha
        _ ↔ H.edge a v₀ v₁ := (he a v₀ v₁ hav hv hvN).symm
  have hHG : H.auxMeetLevel u₀ u₁ v₀ v₁ ≤
      G.auxMeetLevel u₀ u₁ v₀ v₁ :=
    Nat.le_findGreatest
      (H.auxMeetLevel_le_min u₀ u₁ v₀ v₁)
      ((htypes _ (H.auxMeetLevel_le_min u₀ u₁ v₀ v₁)).mp
        (H.auxMeetLevel_agree u₀ u₁ v₀ v₁))
  have hGH : G.auxMeetLevel u₀ u₁ v₀ v₁ ≤
      H.auxMeetLevel u₀ u₁ v₀ v₁ :=
    Nat.le_findGreatest
      (G.auxMeetLevel_le_min u₀ u₁ v₀ v₁)
      ((htypes _ (G.auxMeetLevel_le_min u₀ u₁ v₀ v₁)).mpr
        (G.auxMeetLevel_agree u₀ u₁ v₀ v₁))
  exact Nat.le_antisymm hHG hGH

/-- Capped one-type meets of an infinite graph equal those of its
finite initial segment whenever the two vertices belong to it. -/
theorem initialSegment_oneMeetLevel
    (H : Ordered3Graph Nat) (N u v : Nat)
    (hu : u < N) (hv : v < N) :
    (H.initialSegment N).toOrdered3Graph.oneMeetLevel u v =
      H.oneMeetLevel u v := by
  apply oneMeetLevel_eq_of_edge_iff_below _ H hu hv
  intro a b c hab hbc hcN
  exact H.initialSegment_edge_iff hab hbc hcN

/-- Capped auxiliary meets are also invariant under finite truncation. -/
theorem initialSegment_auxMeetLevel
    (H : Ordered3Graph Nat) (N u₀ u₁ v₀ v₁ : Nat)
    (hu : u₀ < u₁) (huN : u₁ < N)
    (hv : v₀ < v₁) (hvN : v₁ < N) :
    (H.initialSegment N).toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁ =
      H.auxMeetLevel u₀ u₁ v₀ v₁ := by
  apply auxMeetLevel_eq_of_edge_iff_below _ H hu huN hv hvN
  intro a b c hab hbc hcN
  exact H.initialSegment_edge_iff hab hbc hcN

end Ordered3Graph
end ThreeUniformDiaries
