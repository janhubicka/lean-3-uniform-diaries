import ThreeUniformDiaries.DiaryOnePassFiniteSchedule

/-!
# Raw one-pass target hypergraph, with induced old copy

This is the first CONCRETE target relation for the static one-pass
completion scheme. Original edges are copied along the finite-block
enumeration, and each fresh event contributes its correct 0/1 or 0/2
role marker plus precisely the selected original singleton/pair
class-incidence edges.

The inserted edge predicate mentions an event vertex explicitly,
and no event vertex can coincide with an old vertex. Consequently
the old input is an INDUCED ordered subhypergraph, including
reflection of all old nonedges. The proof uses actual finite blocks,
not the old moving-cut insertion algorithm.

Singleton-child order is not yet fixed to decreasing old lexicographic
order. The remaining V1/V2/V3/S1/S2, finite-cut transport, protected
mixed meets, and flip absorption are NOT claimed here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- The index of event i from the block immediately before old m. -/
noncomputable def onePassEventPosition
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length) : Nat :=
  onePassBefore H m + i.val

/-- Each fresh vertex is after the start of its old block
and STRICTLY BEFORE the corresponding old vertex. -/
theorem onePassEventPosition_interval
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length) :
    onePassBefore H m ≤ onePassEventPosition H m i ∧
      onePassEventPosition H m i < onePassOldImage H m := by
  have hi := i.isLt
  dsimp [onePassEventPosition, onePassOldImage]
  omega

/-- Every old vertex k before original m occurs strictly
before all new events of block m. -/
theorem onePassOldImage_lt_before
    (H : Ordered3Graph Nat) (k m : Nat) (hkm : k < m) :
    onePassOldImage H k < onePassBefore H m := by
  cases m with
  | zero => omega
  | succ n =>
    have hkn : k ≤ n := by omega
    have hle : onePassOldImage H k ≤ onePassOldImage H n :=
      (onePassOldImage_strictMono H).monotone hkn
    have hnext := onePassBefore_succ H n
    omega

/-- No fresh event can coincide with any original vertex,
not just with its immediate old parent. -/
theorem onePassEventPosition_ne_oldImage
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length) (k : Nat) :
    onePassEventPosition H m i ≠ onePassOldImage H k := by
  intro heq
  obtain ⟨hlower, hupper⟩ := onePassEventPosition_interval H m i
  by_cases hkm : k < m
  · have hbefore := onePassOldImage_lt_before H k m hkm
    omega
  · have hmk : m ≤ k := by omega
    have hafter : onePassOldImage H m ≤ onePassOldImage H k :=
      (onePassOldImage_strictMono H).monotone hmk
    omega

/-- The actual list entry at an event vertex. -/
noncomputable def onePassEventAt
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length) : BlockEvent :=
  (onePassBlock H m).get i

/-- New edges contributed by one-pass events.
A singleton event is marked (0,1,e) and has (0,e,f(u)) precisely
on its selected original leaf germ. A pair event is marked
(0,2,e) and has (e,f(u),f(v)) on its selected original pair germ.

The outer support clause explicitly records that every inserted
edge contains the fresh event vertex, which is used to prove
inducedness of the old input. -/
noncomputable def onePassInsertedEdge
    (H : Ordered3Graph Nat) (x y z : Nat) : Prop :=
  ∃ (m : Nat) (i : Fin (onePassBlock H m).length),
    (x = onePassEventPosition H m i ∨
     y = onePassEventPosition H m i ∨
     z = onePassEventPosition H m i) ∧
    ((∃ g : OneGermSpace m,
      onePassEventAt H m i = BlockEvent.singleton m g ∧
      ((x = 0 ∧ y = 1 ∧ z = onePassEventPosition H m i) ∨
       ∃ u : Nat, IsLeaf H u ∧ m ≤ u ∧
         oneGermCode H m u = g ∧
         x = 0 ∧ y = onePassEventPosition H m i ∧
         z = onePassOldImage H u))
     ∨
     (∃ g : TwoGermSpace m,
      onePassEventAt H m i = BlockEvent.pair m g ∧
      ((x = 0 ∧ y = 2 ∧ z = onePassEventPosition H m i) ∨
       ∃ u v : Nat, IsLeaf H u ∧ IsLeaf H v ∧
         m ≤ u ∧ u < v ∧ twoGermCode H m u v = g ∧
         x = onePassEventPosition H m i ∧
         y = onePassOldImage H u ∧ z = onePassOldImage H v)))

theorem onePassInsertedEdge_supported
    (H : Ordered3Graph Nat) (x y z : Nat)
    (he : onePassInsertedEdge H x y z) :
    ∃ (m : Nat) (i : Fin (onePassBlock H m).length),
      x = onePassEventPosition H m i ∨
      y = onePassEventPosition H m i ∨
      z = onePassEventPosition H m i := by
  obtain ⟨m, i, hs, _⟩ := he
  exact ⟨m, i, hs⟩

/-- The provisional but CONCRETE target 3-hypergraph.
The original edge relation is copied exactly on old vertices. -/
noncomputable def onePassRawTarget
    (H : Ordered3Graph Nat) : Ordered3Graph Nat where
  edge x y z :=
    (∃ a b c : Nat, H.edge a b c ∧
       x = onePassOldImage H a ∧
       y = onePassOldImage H b ∧
       z = onePassOldImage H c)
    ∨ onePassInsertedEdge H x y z

/-- Exact preservation AND reflection of original edges.
In particular no new event can fill in an old nonedge. -/
theorem onePassRawTarget_edge_image_iff
    (H : Ordered3Graph Nat) (a b c : Nat) :
    (onePassRawTarget H).edge
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) ↔ H.edge a b c := by
  constructor
  · intro he
    rcases he with hOld | hNew
    · obtain ⟨a', b', c', habc, ha, hb, hc⟩ := hOld
      have haa : a = a' := (onePassOldImage_strictMono H).injective ha
      have hbb : b = b' := (onePassOldImage_strictMono H).injective hb
      have hcc : c = c' := (onePassOldImage_strictMono H).injective hc
      rcases haa with rfl
      rcases hbb with rfl
      rcases hcc with rfl
      exact habc
    · obtain ⟨m, i, hs⟩ :=
        onePassInsertedEdge_supported H _ _ _ hNew
      rcases hs with hx | hy | hz
      · exact False.elim
          ((onePassEventPosition_ne_oldImage H m i a) hx.symm)
      · exact False.elim
          ((onePassEventPosition_ne_oldImage H m i b) hy.symm)
      · exact False.elim
          ((onePassEventPosition_ne_oldImage H m i c) hz.symm)
  · intro he
    exact Or.inl ⟨a, b, c, he, rfl, rfl, rfl⟩

/-- The actual one-pass old-vertex map is already an induced
order-preserving embedding into the raw target hypergraph. -/
noncomputable def onePassRawEmbedding
    (H : Ordered3Graph Nat) :
    Ordered3Graph.Embedding H (onePassRawTarget H) where
  toFun := onePassOldImage H
  strictMono := onePassOldImage_strictMono H
  edge_iff := by
    intro a b c _ _
    exact (onePassRawTarget_edge_image_iff H a b c).symm

/-- The singleton event's role marker really is a target edge. -/
theorem onePassRawTarget_singleton_marker
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g) :
    (onePassRawTarget H).edge 0 1 (onePassEventPosition H m i) := by
  apply Or.inr
  refine ⟨m, i, Or.inr (Or.inr rfl), Or.inl ?_⟩
  exact ⟨g, hget, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- The pair event's role marker really is a target edge. -/
theorem onePassRawTarget_pair_marker
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g) :
    (onePassRawTarget H).edge 0 2 (onePassEventPosition H m i) := by
  apply Or.inr
  refine ⟨m, i, Or.inr (Or.inr rfl), Or.inr ?_⟩
  exact ⟨g, hget, Or.inl ⟨rfl, rfl, rfl⟩⟩

end DiaryLeafPriority
end ThreeUniformDiaries
