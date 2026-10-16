import ThreeUniformDiaries.DiaryOnePassConcreteCarrier
import ThreeUniformDiaries.DiaryPrediaryDefinition

/-!
# Ordered support and exact declared incidences in the raw one-pass target

This module is the next mathematical step after the concrete target
carrier and induced-copy theorem. It proves, from the original
pre-diary E axiom, that EVERY copied/inserted target edge is on a
strictly increasing triple. It also exports the actual new role
markers and class-incidence witnesses for both kinds of split.

The input's role-marker edges are reflected exactly at all old
vertices. These are concrete E-shape and old-role preservation
interfaces, not an assertion that the output already satisfies
V1/V2/V3 or the S meet conditions. In particular singleton events
still require the original lexicographic ordering refinement.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- There is no actual event in any of the first three marker
levels, so the cut of a fresh event is at least three. -/
theorem onePassEvent_cut_ge_three
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length) : 3 ≤ m := by
  by_contra hn
  have hm : m < 3 := by omega
  have hi : i.val < 0 := by
    simpa [onePassBlock_markers H m hm] using i.isLt
  omega

/-- All new event vertices are strictly above the distinguished
markers, including when a block contains no other originals. -/
theorem onePassEventPosition_ge_three
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length) :
    3 ≤ onePassEventPosition H m i := by
  have hm := onePassEvent_cut_ge_three H m i
  have hb : m ≤ onePassBefore H m := by
    unfold onePassBefore
    omega
  have hi := (onePassEventPosition_interval H m i).1
  omega

/-- Each event vertex precedes every original leaf eligible for
its m-germ class, not merely the old vertex m itself. -/
theorem onePassEventPosition_lt_oldImage
    (H : Ordered3Graph Nat) (m u : Nat)
    (i : Fin (onePassBlock H m).length) (hmu : m ≤ u) :
    onePassEventPosition H m i < onePassOldImage H u := by
  have hi := (onePassEventPosition_interval H m i).2
  have hu := (onePassOldImage_strictMono H).monotone hmu
  omega

/-- Source V/E alone implies the raw one-pass graph contains
only strictly increasing edges, including ALL new event edges. -/
theorem onePassRawTarget_edge_ordered
    {H : Ordered3Graph Nat} (P : RolePrediary H)
    (x y z : Nat) (he : (onePassRawTarget H).edge x y z) :
    x < y ∧ y < z := by
  rcases he with hOld | hNew
  · obtain ⟨a,b,c,he,rfl,rfl,rfl⟩ := hOld
    obtain ⟨hab,hbc⟩ := P.edge_ordered a b c he
    exact ⟨(onePassOldImage_strictMono H) hab,
      (onePassOldImage_strictMono H) hbc⟩
  · obtain ⟨m,i,_,hOne|hTwo⟩ := hNew
    · obtain ⟨g,hget,hMarker|hInc⟩ := hOne
      · obtain ⟨rfl,rfl,rfl⟩ := hMarker
        have hge := onePassEventPosition_ge_three H m i
        omega
      · obtain ⟨u,hu,hmu,hcode,rfl,rfl,rfl⟩ := hInc
        have hge := onePassEventPosition_ge_three H m i
        have hlt := onePassEventPosition_lt_oldImage H m u i hmu
        omega
    · obtain ⟨g,hget,hMarker|hInc⟩ := hTwo
      · obtain ⟨rfl,rfl,rfl⟩ := hMarker
        have hge := onePassEventPosition_ge_three H m i
        omega
      · obtain ⟨u,v,hu,hv,hmu,huv,hcode,rfl,rfl,rfl⟩ := hInc
        have hlt := onePassEventPosition_lt_oldImage H m u i hmu
        have hafter := (onePassOldImage_strictMono H) huv
        omega

/-- Every selected source singleton class has precisely the
declared positive incidence on an original leaf satisfying its
full m-germ signature. -/
theorem onePassRawTarget_singleton_incidence
    (H : Ordered3Graph Nat) (m u : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g)
    (hu : IsLeaf H u) (hmu : m ≤ u)
    (hcode : oneGermCode H m u = g) :
    (onePassRawTarget H).edge 0
      (onePassEventPosition H m i) (onePassOldImage H u) := by
  apply Or.inr
  refine ⟨m, i, Or.inr (Or.inl rfl), Or.inl ?_⟩
  exact ⟨g, hget, Or.inr ⟨u, hu, hmu, hcode, rfl, rfl, rfl⟩⟩

/-- Every selected source pair class has precisely the declared
positive incidence on an ordered original leaf pair. -/
theorem onePassRawTarget_pair_incidence
    (H : Ordered3Graph Nat) (m u v : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (huv : u < v)
    (hcode : twoGermCode H m u v = g) :
    (onePassRawTarget H).edge
      (onePassEventPosition H m i)
      (onePassOldImage H u) (onePassOldImage H v) := by
  apply Or.inr
  refine ⟨m, i, Or.inl rfl, Or.inr ?_⟩
  exact ⟨g, hget, Or.inr
    ⟨u, v, hu, hv, hmu, huv, hcode, rfl, rfl, rfl⟩⟩

/-- Old 1-role markers are neither lost nor added when
one-pass event edges are inserted. -/
theorem onePassRawTarget_old_marker_one_iff
    (H : Ordered3Graph Nat) (u : Nat) :
    (onePassRawTarget H).edge 0 1 (onePassOldImage H u) ↔
      H.edge 0 1 u := by
  simpa only [onePassOldImage_zero, onePassOldImage_one] using
    (onePassRawTarget_edge_image_iff H 0 1 u)

/-- Old 2-role markers are neither lost nor added. -/
theorem onePassRawTarget_old_marker_two_iff
    (H : Ordered3Graph Nat) (u : Nat) :
    (onePassRawTarget H).edge 0 2 (onePassOldImage H u) ↔
      H.edge 0 2 u := by
  simpa only [onePassOldImage_zero, onePassOldImage_two] using
    (onePassRawTarget_edge_image_iff H 0 2 u)

end DiaryLeafPriority
end ThreeUniformDiaries
