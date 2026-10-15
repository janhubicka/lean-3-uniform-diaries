import ThreeUniformDiaries.DiaryFiniteThreeTailOverlapProfiles
import ThreeUniformDiaries.DiaryOppositeBranchCompatibility
import ThreeUniformDiaries.DiaryFinitePointedEnvelope

/-!
# The two opposite diary native three-tail pictures really glue

This is the first simultaneous finite-picture theorem for the
two different diary orientation classes.

Take an ordered positive leaf pair a<b and negative leaf pair
c<d in a complete V/E/S diary D, and any gappy
type-respecting embedding psi:D -> G.

Write m=a meet b, n=c meet d and j=psi(3).
The verified native three-tail pictures are the induced
hypergraphs on their compressed carriers:

  fPlus  = threeTailInsertion j (psi m) (psi a) (psi b)
  fMinus = threeTailInsertion j (psi n) (psi c) (psi d).

The positive branches are b and c; the negative branches are
a and d. The exact RoleDiary marker identities prove
SameTwoTypeBelow j (psi m,psi b) (psi n,psi c).
That one type equality supplies all THREE overlap profile
components: split vertex, central leaf, and mixed split/leaf.
The fourth component is the common fixed generic prefix.

Consequently the edge-level ordered free amalgam of the two
three-tail sources exists, with four exterior positions:
split, negative leaf, positive central leaf, negative leaf.
The first native source is the literal initial subpicture
and the second is induced under the one-position shift.

The remaining work is the FINITE ATR embedding check under the
inserted vertex, followed by a prefix-fixing generic
type-respecting copy. This theorem does not assume either
and does not claim global orientation synchronisation.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {H : Ordered3Graph Nat}

/-- Exact edge-overlap compatibility for the TWO ACTUAL
compressed native three-tail source pictures arising from
oppositely oriented diary leaf pairs. Every target generic
prefix level skipped by psi remains visible in this proof. -/
theorem oppositeLex_native_threeTail_overlap
    (D : RoleDiary H)
    (G : GenericEnumerated3Graph)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hplus : LexEarlier H a b)
    (hminus : ¬ LexEarlier H c d) :
    let j := ψ 3
    let m := H.oneMeetLevel a b
    let n := H.oneMeetLevel c d
    let fPlus := threeTailInsertion j (ψ m) (ψ a) (ψ b)
    let fMinus := threeTailInsertion j (ψ n) (ψ c) (ψ d)
    ThreeTailOverlapCompatible
      (G.graph.pullback fPlus) (G.graph.pullback fMinus) j := by
  let j := ψ 3
  let m := H.oneMeetLevel a b
  let n := H.oneMeetLevel c d
  let fPlus := threeTailInsertion j (ψ m) (ψ a) (ψ b)
  let fMinus := threeTailInsertion j (ψ n) (ψ c) (ψ d)
  have hType : G.graph.SameTwoTypeBelow j
      (ψ m) (ψ b) (ψ n) (ψ c) :=
    (D.oppositeLex_same_branch_profiles_in_generic
      G ψ hψ a b c d hab hcd ha hb hc hd hplus hminus).1
  have hPrefix :
      ∀ x y z, x < y → y < z → z < j →
        ((G.graph.pullback fPlus).edge x y z ↔
         (G.graph.pullback fMinus).edge x y z) := by
    intro x y z hxy hyz hz
    change G.graph.edge (fPlus x) (fPlus y) (fPlus z) ↔
      G.graph.edge (fMinus x) (fMinus y) (fMinus z)
    have hx : x < j := by omega
    have hy : y < j := by omega
    simp only [fPlus, fMinus,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) x hx,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) y hy,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) z hz,
      threeTailInsertion_fix_prefix j (ψ n) (ψ c) (ψ d) x hx,
      threeTailInsertion_fix_prefix j (ψ n) (ψ c) (ψ d) y hy,
      threeTailInsertion_fix_prefix j (ψ n) (ψ c) (ψ d) z hz]
  have hSplit :
      ∀ x y, x < y → y < j →
        ((G.graph.pullback fPlus).edge x y j ↔
         (G.graph.pullback fMinus).edge x y j) := by
    intro x y hxy hy
    change G.graph.edge (fPlus x) (fPlus y) (fPlus j) ↔
      G.graph.edge (fMinus x) (fMinus y) (fMinus j)
    have hx : x < j := by omega
    simpa only [fPlus, fMinus,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) x hx,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) y hy,
      threeTailInsertion_fix_prefix j (ψ n) (ψ c) (ψ d) x hx,
      threeTailInsertion_fix_prefix j (ψ n) (ψ c) (ψ d) y hy,
      threeTailInsertion_split j (ψ m) (ψ a) (ψ b),
      threeTailInsertion_split j (ψ n) (ψ c) (ψ d)] using
        hType.1 hxy hy
  have hCenter :
      ∀ x y, x < y → y < j →
        ((G.graph.pullback fPlus).edge x y (j+2) ↔
         (G.graph.pullback fMinus).edge x y (j+1)) := by
    intro x y hxy hy
    change G.graph.edge (fPlus x) (fPlus y) (fPlus (j+2)) ↔
      G.graph.edge (fMinus x) (fMinus y) (fMinus (j+1))
    have hx : x < j := by omega
    simpa only [fPlus, fMinus,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) x hx,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) y hy,
      threeTailInsertion_fix_prefix j (ψ n) (ψ c) (ψ d) x hx,
      threeTailInsertion_fix_prefix j (ψ n) (ψ c) (ψ d) y hy,
      threeTailInsertion_second j (ψ m) (ψ a) (ψ b),
      threeTailInsertion_first j (ψ n) (ψ c) (ψ d)] using
        hType.2.1 hxy hy
  have hMixed :
      ∀ x, x < j →
        ((G.graph.pullback fPlus).edge x j (j+2) ↔
         (G.graph.pullback fMinus).edge x j (j+1)) := by
    intro x hx
    change G.graph.edge (fPlus x) (fPlus j) (fPlus (j+2)) ↔
      G.graph.edge (fMinus x) (fMinus j) (fMinus (j+1))
    simpa only [fPlus, fMinus,
      threeTailInsertion_fix_prefix j (ψ m) (ψ a) (ψ b) x hx,
      threeTailInsertion_fix_prefix j (ψ n) (ψ c) (ψ d) x hx,
      threeTailInsertion_split j (ψ m) (ψ a) (ψ b),
      threeTailInsertion_split j (ψ n) (ψ c) (ψ d),
      threeTailInsertion_second j (ψ m) (ψ a) (ψ b),
      threeTailInsertion_first j (ψ n) (ψ c) (ψ d)] using
        (hType.2.2 (a := x) hx)
  exact threeTailOverlapCompatible_of_profiles
    (G.graph.pullback fPlus) (G.graph.pullback fMinus) j
    hPrefix hSplit hCenter hMixed

/-- The two oppositely oriented diary native finite pictures
have a literal four-tail ordered EDGE amalgam, with both
original sources induced. This follows from actual source
profile compatibility, not a synthetic amalgamation axiom. -/
theorem oppositeLex_native_fourTail_edge_amalgam
    (D : RoleDiary H)
    (G : GenericEnumerated3Graph)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hplus : LexEarlier H a b)
    (hminus : ¬ LexEarlier H c d) :
    let j := ψ 3
    let m := H.oneMeetLevel a b
    let n := H.oneMeetLevel c d
    let A := G.graph.pullback
      (threeTailInsertion j (ψ m) (ψ a) (ψ b))
    let B := G.graph.pullback
      (threeTailInsertion j (ψ n) (ψ c) (ψ d))
    let C := threeTailFreeAmalgam A B j
    (∀ x y z, z < j+3 → (C.edge x y z ↔ A.edge x y z)) ∧
    (∀ x y z, x < y → y < z → z < j+3 →
      (C.edge (threeTailShift j x)
        (threeTailShift j y) (threeTailShift j z) ↔
       B.edge x y z)) := by
  let j := ψ 3
  let m := H.oneMeetLevel a b
  let n := H.oneMeetLevel c d
  let A := G.graph.pullback
    (threeTailInsertion j (ψ m) (ψ a) (ψ b))
  let B := G.graph.pullback
    (threeTailInsertion j (ψ n) (ψ c) (ψ d))
  let C := threeTailFreeAmalgam A B j
  have hOverlap : ThreeTailOverlapCompatible A B j :=
    D.oppositeLex_native_threeTail_overlap
      G ψ hψ a b c d hab hcd ha hb hc hd hplus hminus
  constructor
  · intro x y z hz
    exact threeTailFreeAmalgam_left A B j x y z hz
  · intro x y z hxy hyz hz
    exact threeTailFreeAmalgam_right A B j hOverlap x y z hxy hyz hz

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
