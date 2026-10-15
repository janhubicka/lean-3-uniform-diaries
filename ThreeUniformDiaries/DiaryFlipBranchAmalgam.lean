import ThreeUniformDiaries.DiaryFlipPrefixReconstruction

/-!
# An induced tree of branches for coherent diary flips

The finite flip-prefix reconstruction theorem implies that the
edge relation on a branch is determined by the flip word at all
levels strictly below the last vertex of a triple.

We can therefore identify shared prefix vertices of different
diary flips, and define the hyperedges of the resulting forest
by existence of an edge in one actual flip branch. The edge
relation is unambiguous where two branches share a vertex:
the prefix-reconstruction theorem transfers the edge bit.

IMPORTANT: this is only the induced relational amalgam.
It is not yet a pre-diary. Incomparable leaves need cross-branch
marker edges (1,u,v) or (2,u,v), and V1/V2 coherence and
type-meet transfer must be checked after adding those edges.
The naive free union of branch edge sets does not do this.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

/-- A family of genuine V/E/S diary flips of ONE source diary.
The identity pre-embeddings preserve the leaf type meets only;
they are not assumed to preserve mixed split/leaf meets. -/
structure FlipFamily (A : Ordered3Graph Nat) (ι : Type*) where
  sourceDiary : RoleDiary A
  graph : ι → Ordered3Graph Nat
  targetDiary : ∀ i, RoleDiary (graph i)
  isFlip : ∀ i, DiaryPreembeddingSpec A (graph i) id

namespace FlipFamily

variable {A : Ordered3Graph Nat} {ι : Type*}

/-- The actual asymmetric deleted-positive 1-split bit. -/
noncomputable def oneBit (T : FlipFamily A ι) (i : ι) (m : Nat) : Bool := by
  classical
  exact decide (OneSplitRemovedBit A (T.graph i) m)

/-- The corresponding 2-split bit. -/
noncomputable def twoBit (T : FlipFamily A ι) (i : ι) (m : Nat) : Bool := by
  classical
  exact decide (TwoSplitRemovedBit A (T.graph i) m)

/-- Finite prefix codes, represented as masked infinite Boolean
functions. The mask is false above the level, so a node is
determined by its finitely many earlier control bits. -/
abbrev FlipNode := Nat × ((Nat → Bool) × (Nat → Bool))

noncomputable def node (T : FlipFamily A ι) (i : ι) (n : Nat) :
    FlipNode :=
  (n, (fun m => if m < n then T.oneBit i m else false,
       fun m => if m < n then T.twoBit i m else false))

/-- The node remembers its exact integer level. -/
theorem node_level (T : FlipFamily A ι) (i : ι) (n : Nat) :
    (T.node i n).1 = n := rfl

/-- When two branch nodes coincide, their one-split bits agree
at every genuinely earlier source level. -/
theorem oneBit_eq_of_node_eq
    (T : FlipFamily A ι) (i j : ι) (n m : Nat)
    (hnode : T.node i n = T.node j n) (hm : m < n) :
    T.oneBit i m = T.oneBit j m := by
  have heq := congrArg (fun x : FlipNode => x.2.1) hnode
  have heqM := congrFun heq m
  simpa only [node, if_pos hm] using heqM

/-- Likewise for source-relative 2-split flip bits. -/
theorem twoBit_eq_of_node_eq
    (T : FlipFamily A ι) (i j : ι) (n m : Nat)
    (hnode : T.node i n = T.node j n) (hm : m < n) :
    T.twoBit i m = T.twoBit j m := by
  have heq := congrArg (fun x : FlipNode => x.2.2) hnode
  have heqM := congrFun heq m
  simpa only [node, if_pos hm] using heqM

/-- Equality of coded one-split bits is exactly the Prop
agreement used in the genuine reconstruction theorem. -/
theorem one_control_of_node_eq
    (T : FlipFamily A ι) (i j : ι) (n m : Nat)
    (hnode : T.node i n = T.node j n) (hm : m < n) :
    OneSplitRemovedBit A (T.graph i) m ↔
      OneSplitRemovedBit A (T.graph j) m := by
  classical
  have h := T.oneBit_eq_of_node_eq i j n m hnode hm
  unfold oneBit at h
  by_cases ha : OneSplitRemovedBit A (T.graph i) m <;>
    by_cases hb : OneSplitRemovedBit A (T.graph j) m <;>
    simp_all

theorem two_control_of_node_eq
    (T : FlipFamily A ι) (i j : ι) (n m : Nat)
    (hnode : T.node i n = T.node j n) (hm : m < n) :
    TwoSplitRemovedBit A (T.graph i) m ↔
      TwoSplitRemovedBit A (T.graph j) m := by
  classical
  have h := T.twoBit_eq_of_node_eq i j n m hnode hm
  unfold twoBit at h
  by_cases ha : TwoSplitRemovedBit A (T.graph i) m <;>
    by_cases hb : TwoSplitRemovedBit A (T.graph j) m <;>
    simp_all

/-- The exact branch-amalgamation compatibility statement:
two flips agreeing at their z-prefix have identical edges on
all increasing triples x<y<z of their respective branches. -/
theorem edge_agree_of_shared_terminal_node
    (T : FlipFamily A ι) (i j : ι)
    (x y z : Nat) (hxy : x < y) (hyz : y < z)
    (hnode : T.node i z = T.node j z) :
    (T.graph i).edge x y z ↔ (T.graph j).edge x y z := by
  have hOne : ∀ m, m < z → IsOneSplit A m →
        (OneSplitRemovedBit A (T.graph i) m ↔
         OneSplitRemovedBit A (T.graph j) m) := by
    intro m hm _
    exact T.one_control_of_node_eq i j z m hnode hm
  have hTwo : ∀ m, m < z → IsTwoSplit A m →
        (TwoSplitRemovedBit A (T.graph i) m ↔
         TwoSplitRemovedBit A (T.graph j) m) := by
    intro m hm _
    exact T.two_control_of_node_eq i j z m hnode hm
  exact T.sourceDiary.two_flips_edge_iff_of_control_prefix
    (T.targetDiary i) (T.targetDiary j)
    (T.isFlip i) (T.isFlip j) z hOne hTwo
    x y z hxy hyz (Or.inl hyz)

/-- A triple of prefix nodes is declared an edge precisely if
it is the image of an increasing edge in at least one branch.
There are NO invented cross-branch hyperedges in this object. -/
def branchAmalgam (T : FlipFamily A ι) :
    Ordered3Graph FlipNode where
  edge X Y Z :=
    ∃ (i : ι) (x y z : Nat),
      x < y ∧ y < z ∧
      T.node i x = X ∧ T.node i y = Y ∧ T.node i z = Z ∧
      (T.graph i).edge x y z

/-- Every branch is induced in this relational amalgam.
The forward direction is nontrivial: another branch
witnessing the same nodes must have the same terminal
prefix bits, hence the same original increasing edge. -/
theorem branchAmalgam_edge_iff
    (T : FlipFamily A ι) (i : ι)
    (x y z : Nat) (hxy : x < y) (hyz : y < z) :
    (T.branchAmalgam).edge
        (T.node i x) (T.node i y) (T.node i z) ↔
      (T.graph i).edge x y z := by
  constructor
  · rintro ⟨j, x', y', z', hxy', hyz', hx, hy, hz, hedge⟩
    have ex : x' = x := by
      have hh := congrArg Prod.fst hx
      simpa only [node] using hh
    have ey : y' = y := by
      have hh := congrArg Prod.fst hy
      simpa only [node] using hh
    have ez : z' = z := by
      have hh := congrArg Prod.fst hz
      simpa only [node] using hh
    subst x'
    subst y'
    subst z'
    exact (T.edge_agree_of_shared_terminal_node
      j i x y z hxy hyz hz).mp hedge
  · intro hedge
    exact ⟨i, x, y, z, hxy, hyz,
      rfl, rfl, rfl, hedge⟩

end FlipFamily
end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
