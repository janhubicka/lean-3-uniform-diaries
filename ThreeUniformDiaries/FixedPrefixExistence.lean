import ThreeUniformDiaries.FixedPrefixCountableEmbedding

/-!
# An induced generic embedding fixing any prescribed common initial segment

The fixed-prefix inherited construction requires a parent in its
initial stage. Consequently the apparent zero-prefix parent-schedule
interface has no terms (already at stage zero), and that interface
must not be mistaken for an existence result at n=0.

This file combines two independently verified recursions:
* for n=0, begin with the unique one-vertex root;
* for n>0, begin with the literal n-vertex identity stage.

The result is a genuine *existence* theorem for every finite common
initial segment, not just a theorem conditional on a supplied schedule.
It does not yet guarantee aux-type-respecting meets.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

/-- There is no parent schedule starting from an empty stage. -/
theorem no_empty_prefix_parent_schedule
    (parent : PrefixParentSchedule 0) : False :=
  Fin.elim0 (parent 0)

/-- For a nonempty initial segment of size k+1, use the immediately
preceding source index as the parent of every newly added vertex. -/
def consecutivePrefixParents (k : Nat) :
    PrefixParentSchedule (k + 1) :=
  fun t => ⟨k + t, by omega⟩

/-- The generic hypergraph contains an induced, order-preserving copy
of any enumerated 3-graph which agrees with it on the first n
vertices, and the copy fixes all those first n vertices.

This is the existence layer needed by the K_I construction; the
separate parent schedule for K_I must also ensure exact type meets. -/
theorem exists_induced_embedding_fixing_prefix
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (n : Nat)
    (hI : K.initialSegment n = G.graph.initialSegment n) :
    ∃ f : Nat → Nat,
      StrictMono f ∧
      (∀ i : Nat, i < n → f i = i) ∧
      (∀ a b c : Nat, a < b → b < c →
        (K.edge a b c ↔
          G.graph.edge (f a) (f b) (f c))) := by
  cases n with
  | zero =>
      let parent : ParentSchedule := fun k => Fin.last k
      have h := G.exists_countable_inherited_embedding K parent
      refine ⟨G.inheritedEmbedding K parent, h.1, ?_, h.2⟩
      intro i hi
      omega
  | succ k =>
      let parent := consecutivePrefixParents k
      have h := G.fixedInheritedEmbedding_isEmbedding
        K (k + 1) hI parent
      exact ⟨G.fixedInheritedEmbedding K (k + 1) hI parent,
        h.1, h.2.1, h.2.2⟩

end GenericEnumerated3Graph
end ThreeUniformDiaries
