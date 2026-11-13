import ThreeUniformDiaries.DiaryGenericMixedConeIndivisibility
import ThreeUniformDiaries.DiaryChosenOldSupportSaturatedGoodColour

/-!
# Track D: a finite family hitting every generic subcopy has a generic good member

This is a sharp, **conditional** reduction of the remaining generic-fibre
obstruction. Suppose finitely many predicates Good(i,·) jointly meet every
auxiliary-type-respecting induced generic selfcopy. Colour each vertex by
the entire subset of indices i at which Good(i,·) holds. The verified
finite-vertex-colour indivisibility theorem produces a generic selfcopy
with a CONSTANT subset. This subset cannot be empty, by the hitting
hypothesis. Hence one fixed i is good at EVERY vertex of that generic
selfcopy.

Applied to genuine reserved immediate successors, if a FINITE supplied
family of complete old-support stages hits EVERY generic selfcopy, one
of those old supports has a WHOLE induced generic next-leaf cone in the
original prescribed F range. This result makes the precise missing
finite-family hitting hypothesis explicit. The existing chosen cofinal
old-support theorem does NOT provide that hypothesis.

No assertion is made that arbitrary cofinal or deep S1-cone recurrence
implies genericity, that there is a uniformly bounded family of old
supports, or that an immediate successor persists through later source
horizons. The frozen manuscript is unchanged.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finite family of unary vertex predicates meeting EVERY actual
aux-type-respecting induced generic selfcopy has ONE member holding on
an ENTIRE induced generic selfcopy. The family may be empty as a type;
then the hitting hypothesis is inconsistent.

This is a direct consequence of generic finite-vertex-colour
indivisibility, not a new relative diary extension principle. -/
theorem GenericEnumerated3Graph.exists_generic_copy_in_one_finitely_hitting_piece
    (G : GenericEnumerated3Graph)
    {ι : Type} [Fintype ι]
    (Good : ι → Nat → Prop)
    (hHit : ∀ u : Ordered3Graph.Embedding G.graph G.graph,
      u.AuxTypeRespecting → ∃ i : ι, ∃ n : Nat, Good i (u n)) :
    ∃ i : ι, ∃ u : Ordered3Graph.Embedding G.graph G.graph,
      u.AuxTypeRespecting ∧ ∀ n : Nat, Good i (u n) := by
  classical
  let colour : Nat → Finset ι :=
    fun n => Finset.univ.filter (fun i : ι => Good i n)
  obtain ⟨u, hu, p, hp⟩ :=
    generic_finite_vertex_colouring_monochromatic G colour
  obtain ⟨i, n, hi⟩ := hHit u hu
  have hInColour : i ∈ colour (u n) := by
    change i ∈ (Finset.univ : Finset ι).filter
      (fun j : ι => Good j (u n))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have hInP : i ∈ p := by
    rw [← hp n]
    exact hInColour
  refine ⟨i, u, hu, ?_⟩
  intro n'
  have hInColour' : i ∈ colour (u n') := by
    rw [hp n']
    exact hInP
  change i ∈ (Finset.univ : Finset ι).filter
    (fun j : ι => Good j (u n')) at hInColour'
  exact (Finset.mem_filter.mp hInColour').2

/-- Track D's exact finite-family interface. A SUPPLIED finite list of
genuine complete old reserved stages is assumed to hit EVERY induced
aux-type-respecting generic selfcopy by at least ONE actual compatible
immediate successor. One fixed listed stage then has an ENTIRE induced
generic cone of such successors. No bound on the necessary old stages
and no source-horizon persistence is obtained by this theorem. -/
theorem generic_reserved_next_leaf_cone_of_finitely_hitting_old_stages
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m k : Nat)
    (stages : Fin k → Nat → Nat)
    (hStages : ∀ i : Fin k,
      ReservedDiaryStage H K (fun t : Nat => F t) m (stages i))
    (hHit : ∀ u : Ordered3Graph.Embedding G.graph G.graph,
      u.AuxTypeRespecting →
      ∃ i : Fin k, ∃ n : Nat,
        HasCompatibleReservedNextLeaf H K
          (fun t : Nat => F t) (stages i) m (F (u n))) :
    ∃ i : Fin k, ∃ u : Ordered3Graph.Embedding G.graph G.graph,
      ReservedDiaryStage H K (fun t : Nat => F t) m (stages i) ∧
      u.AuxTypeRespecting ∧
      ∀ n : Nat,
        IsLeaf K (F (u n)) ∧
        HasCompatibleReservedNextLeaf H K
          (fun t : Nat => F t) (stages i) m (F (u n)) := by
  obtain ⟨i, u, hu, hAll⟩ :=
    G.exists_generic_copy_in_one_finitely_hitting_piece
      (fun i : Fin k => fun n : Nat =>
        HasCompatibleReservedNextLeaf H K
          (fun t : Nat => F t) (stages i) m (F n))
      hHit
  exact ⟨i, u, hStages i, hu, fun n => ⟨hFLeaf (u n), hAll n⟩⟩

end DiaryLeafPriority
end ThreeUniformDiaries
