import ThreeUniformDiaries.DiaryLateSingletonATRCodes
import ThreeUniformDiaries.GenericExtensionStep

/-!
# A finite complete list of generic singleton-envelope types at a cut

A singleton type below n is determined by a Boolean edge mask on
pairs from Fin n. There are finitely many such masks. For each mask
choose one generic extension vertex at/after n; the resulting list
contains a representative of EVERY singleton type at n.

The corresponding native finite singleton-envelope EnumNode source
is determined by this type. Thus the same finite list also covers
all genuine ATR source shapes of prefix-plus-one envelopes.

The list is a canonical finite family in the metatheoretic sense
(Classical.choose is used to select its witnesses); its members
need not be distinct. No order on the outer target is assumed.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

open Ordered3Graph

/-- The complete finite Boolean singleton edge mask on pairs in the
protected prefix. Entries outside increasing pairs are harmless. -/
noncomputable def singletonMask
    (G : GenericEnumerated3Graph) (n a : Nat) :
    Fin n → Fin n → Bool := by
  classical
  exact fun x y => decide (G.graph.edge x.val y.val a)

/-- Choose an actual generic realisation of a prescribed finite
singleton mask after the prefix n. -/
noncomputable def singletonRepresentative
    (G : GenericEnumerated3Graph) (n : Nat)
    (p : Fin n → Fin n → Bool) : Nat :=
  Classical.choose (G.extension n p)

theorem singletonRepresentative_spec
    (G : GenericEnumerated3Graph) (n : Nat)
    (p : Fin n → Fin n → Bool) :
    n ≤ G.singletonRepresentative n p ∧
    ∀ x y : Fin n, x < y →
      (G.graph.edge x.val y.val (G.singletonRepresentative n p) ↔
        p x y = true) := by
  exact Classical.choose_spec (G.extension n p)

/-- The generic representative of the mask extracted from a vertex
has exactly that vertex's singleton type over n. -/
theorem singletonRepresentative_sameOneType
    (G : GenericEnumerated3Graph) (n a : Nat) :
    G.graph.SameOneTypeBelow n a
      (G.singletonRepresentative n (G.singletonMask n a)) := by
  classical
  intro x y hxy hyn
  have hxn : x < n := lt_trans hxy hyn
  have hbit :=
    (G.singletonRepresentative_spec n (G.singletonMask n a)).2
      (⟨x, hxn⟩ : Fin n) (⟨y, hyn⟩ : Fin n) hxy
  change G.graph.edge x y
      (G.singletonRepresentative n (G.singletonMask n a)) ↔
      G.singletonMask n a ⟨x, hxn⟩ ⟨y, hyn⟩ = true at hbit
  constructor
  · intro h
    have hp := hbit.mp h
    simpa [singletonMask] using hp
  · intro h
    apply hbit.mpr
    simpa [singletonMask] using h

/-- Enumerate representatives of ALL masks, hence of all singleton
types over n. The finite function type has its standard Fintype. -/
noncomputable def singletonTypeRepresentatives
    (G : GenericEnumerated3Graph) (n : Nat) : List Nat := by
  classical
  exact (Finset.univ : Finset (Fin n → Fin n → Bool)).toList.map
    (fun p => G.singletonRepresentative n p)

theorem singletonRepresentative_mem
    (G : GenericEnumerated3Graph) (n : Nat)
    (p : Fin n → Fin n → Bool) :
    G.singletonRepresentative n p ∈
      G.singletonTypeRepresentatives n := by
  classical
  unfold singletonTypeRepresentatives
  apply List.mem_map.mpr
  exact ⟨p, by simp, rfl⟩

/-- Every singleton type has a member of the finite representative
list, and that member lies after the full protected prefix. -/
theorem singletonTypeRepresentatives_cover
    (G : GenericEnumerated3Graph) (n a : Nat) :
    ∃ b, b ∈ G.singletonTypeRepresentatives n ∧
      n ≤ b ∧ G.graph.SameOneTypeBelow n a b := by
  let p := G.singletonMask n a
  refine ⟨G.singletonRepresentative n p, ?_, ?_, ?_⟩
  · exact G.singletonRepresentative_mem n p
  · exact (G.singletonRepresentative_spec n p).1
  · exact G.singletonRepresentative_sameOneType n a

/-- The same finite representative list covers all NATIVE finite
singleton-envelope source pictures, not merely abstract 1-types.
Both pictured sources retain precisely the first n+1 vertices. -/
theorem singletonTypeRepresentatives_cover_finiteEnum
    (G : GenericEnumerated3Graph) (n a : Nat) (hna : n ≤ a) :
    ∃ (b : Nat), ∃ (hmem : b ∈ G.singletonTypeRepresentatives n),
    ∃ (hnb : n ≤ b),
      (FiniteSingletonEnvelope.ofVertex G.graph n a hna).finiteEnum =
      (FiniteSingletonEnvelope.ofVertex G.graph n b hnb).finiteEnum := by
  obtain ⟨b, hmem, hnb, htype⟩ :=
    G.singletonTypeRepresentatives_cover n a
  refine ⟨b, hmem, hnb, ?_⟩
  let E := FiniteSingletonEnvelope.ofVertex G.graph n a hna
  let T := FiniteSingletonEnvelope.ofVertex G.graph n b hnb
  exact E.finiteEnum_eq_of_sameOneType T htype

end GenericEnumerated3Graph
end ThreeUniformDiaries
