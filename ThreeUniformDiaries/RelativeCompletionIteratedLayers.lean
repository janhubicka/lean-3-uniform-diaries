import ThreeUniformDiaries.RelativeCompletionNextLayer

/-!
# Iterated protected layers wholly inside a strong coordinate picture

The relative next-layer construction retains all prescribed E-nodes
and saturates each successor cone of U. Iterate it along an arbitrary
strictly increasing sequence g of U-relative levels.

At every stage:
* all chosen nodes lie inside U;
* they occupy exactly ambient level f(g k);
* the layer is finite;
* each retained U-child cone is represented uniquely;
* every future E-node is protected, hence appears literally at its
  selected level.

This is the relative analogue of FiniteCompletionIteratedLayers,
and prepares the finite / infinite relative strong-completion theorem.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Protected layers along relative U-levels g(0),g(1),...
without leaving U at skipped relative or ambient levels. -/
noncomputable def relativeCompletionLayers
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) : Nat → Set CoordNode
  | 0 => {r}
  | k + 1 =>
      relativeNextLayer hU E
        (relativeCompletionLayers hU E g hg r k)
        (g k) (g (k + 1))
        (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k)))

/-- Every relative completion layer lives on its prescribed ambient
level f(g k). -/
theorem relativeCompletionLayers_level
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (hrLevel : level r = f (g 0))
    (k : Nat) (x : CoordNode)
    (hx : x ∈ relativeCompletionLayers hU E g hg r k) :
    level x = f (g k) := by
  induction k with
  | zero =>
      change x ∈ ({r} : Set CoordNode) at hx
      have heq : x = r := by simpa using hx
      simpa [heq] using hrLevel
  | succ k ih =>
      change x ∈ relativeNextLayer hU E
        (relativeCompletionLayers hU E g hg r k)
        (g k) (g (k + 1))
        (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k))) at hx
      exact relativeNextLayer_level hU E
        (relativeCompletionLayers hU E g hg r k)
        (g k) (g (k + 1))
        (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k))) x hx

/-- All selected layers stay literally inside U. -/
theorem relativeCompletionLayers_subset
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E : Set CoordNode) (hEU : E ⊆ U)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (hr : r ∈ U)
    (k : Nat) :
    relativeCompletionLayers hU E g hg r k ⊆ U := by
  intro x hx
  cases k with
  | zero =>
      change x ∈ ({r} : Set CoordNode) at hx
      have hxr : x = r := by simpa using hx
      simpa [hxr] using hr
  | succ k =>
      change x ∈ relativeNextLayer hU E
        (relativeCompletionLayers hU E g hg r k)
        (g k) (g (k + 1))
        (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k))) at hx
      exact relativeNextLayer_subset hU hf hrootLevel E
        (relativeCompletionLayers hU E g hg r k) hEU
        (g k) (g (k + 1))
        (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k))) hx

/-- Every finite relative layer has finitely many nodes. -/
theorem relativeCompletionLayers_finite
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (k : Nat) :
    (relativeCompletionLayers hU E g hg r k).Finite := by
  cases k with
  | zero =>
      change ({r} : Set CoordNode).Finite
      exact Set.finite_singleton r
  | succ k =>
      exact relativeNextLayer_finite hU E
        (relativeCompletionLayers hU E g hg r k)
        (g k) (g (k + 1))
        (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k)))

/-- Relative branching at each selected level: exactly one chosen
node in every retained U-child cone of a selected parent. -/
theorem relativeCompletionLayers_unique_child
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (hrLevel : level r = f (g 0))
    (k : Nat)
    (p : CoordNode)
    (hp : p ∈ relativeCompletionLayers hU E g hg r k)
    (t : CoordNode) (ht : t ∈ U)
    (htLevel : level t = f (g k + 1)) (hpt : p ≤ t) :
    ∃! z : CoordNode,
      z ∈ relativeCompletionLayers hU E g hg r (k + 1) ∧
      t ≤ z := by
  change ∃! z : CoordNode,
    z ∈ relativeNextLayer hU E
      (relativeCompletionLayers hU E g hg r k)
      (g k) (g (k + 1))
      (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k))) ∧
    t ≤ z
  exact relativeNextLayer_unique_child hU hf E
    (relativeCompletionLayers hU E g hg r k)
    (g k) (g (k + 1))
    (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k)))
    p hp
    (relativeCompletionLayers_level hU E g hg r hrLevel k p hp)
    t ht htLevel hpt

/-- Chosen nodes at the next relative level have previous-layer
ancestors, so the layer iteration forms a genuine tree. -/
theorem relativeCompletionLayers_has_parent
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (k : Nat) (z : CoordNode)
    (hz : z ∈ relativeCompletionLayers hU E g hg r (k + 1)) :
    ∃ p : CoordNode,
      p ∈ relativeCompletionLayers hU E g hg r k ∧ p ≤ z := by
  change z ∈ relativeNextLayer hU E
    (relativeCompletionLayers hU E g hg r k)
    (g k) (g (k + 1))
    (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k))) at hz
  exact relativeNextLayer_has_parent hU hf E
    (relativeCompletionLayers hU E g hg r k)
    (g k) (g (k + 1))
    (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k))) z hz

/-- Every future prescribed E-node has a retained selected ancestor
at each relative level no later than its own level. -/
theorem relativeCompletionLayers_protects
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E : Set CoordNode) (hE : MeetClosed E) (hEU : E ⊆ U)
    (g : Nat → Nat) (hg : StrictMono g)
    (hgap : ∀ k, AvoidsOpenLevelGap E (f (g k)) (f (g (k + 1))))
    (r : CoordNode) (hr : r ∈ U)
    (hrLevel : level r = f (g 0))
    (hrBelow : ∀ x ∈ E, r ≤ x)
    (k : Nat) (x : CoordNode) (hx : x ∈ E)
    (hxLevel : f (g k) ≤ level x) :
    ∃ p : CoordNode,
      p ∈ relativeCompletionLayers hU E g hg r k ∧ p ≤ x := by
  induction k with
  | zero =>
      exact ⟨r, by simp [relativeCompletionLayers], hrBelow x hx⟩
  | succ k ih =>
      have hprev : f (g k) ≤ level x := by
        have hlt : f (g k) < f (g (k + 1)) :=
          hf (hg (Nat.lt_succ_self k))
        omega
      obtain ⟨p, hp, hpx⟩ := ih hprev
      have hpU : p ∈ U :=
        (relativeCompletionLayers_subset hU hf hrootLevel
          E hEU g hg r hr k) hp
      have hpLevel : level p = f (g k) :=
        relativeCompletionLayers_level hU E g hg r hrLevel k p hp
      change ∃ z : CoordNode,
        z ∈ relativeNextLayer hU E
          (relativeCompletionLayers hU E g hg r k)
          (g k) (g (k + 1))
          (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k))) ∧
        z ≤ x
      exact relativeNextLayer_protects hU hf hrootLevel E
        (relativeCompletionLayers hU E g hg r k)
        hE hEU (g k) (g (k + 1))
        (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k)))
        (hgap k) p hp hpU hpLevel x hx hpx hxLevel

/-- All prescribed E-nodes at selected levels appear literally in
the iterated relative completion, not merely as embedded copies. -/
theorem relativeCompletionLayers_contains_prescribed
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E : Set CoordNode) (hE : MeetClosed E) (hEU : E ⊆ U)
    (g : Nat → Nat) (hg : StrictMono g)
    (hgap : ∀ k, AvoidsOpenLevelGap E (f (g k)) (f (g (k + 1))))
    (r : CoordNode) (hr : r ∈ U)
    (hrLevel : level r = f (g 0))
    (hrBelow : ∀ x ∈ E, r ≤ x)
    (k : Nat) (x : CoordNode) (hx : x ∈ E)
    (hxLevel : level x = f (g k)) :
    x ∈ relativeCompletionLayers hU E g hg r k := by
  obtain ⟨p, hp, hpx⟩ :=
    relativeCompletionLayers_protects hU hf hrootLevel E hE hEU
      g hg hgap r hr hrLevel hrBelow k x hx (by rw [hxLevel])
  have hpLevel :=
    relativeCompletionLayers_level hU E g hg r hrLevel k p hp
  have hEq : p = x :=
    eq_of_le_of_level_eq hpx (hpLevel.trans hxLevel.symm)
  rw [← hEq]
  exact hp

/-- Each relative completed layer is nonempty. The surrounding U is
pruned at all selected relative levels, and the next-layer
construction fills each one of its relative child cones. -/
theorem relativeCompletionLayers_nonempty
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E : Set CoordNode) (hEU : E ⊆ U)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (hr : r ∈ U)
    (hrLevel : level r = f (g 0))
    (k : Nat) :
    (relativeCompletionLayers hU E g hg r k).Nonempty := by
  induction k with
  | zero =>
      exact ⟨r, by simp [relativeCompletionLayers]⟩
  | succ k ih =>
      obtain ⟨p, hp⟩ := ih
      have hpU : p ∈ U :=
        (relativeCompletionLayers_subset hU hf hrootLevel
          E hEU g hg r hr k) hp
      have hpLevel : level p = f (g k) :=
        relativeCompletionLayers_level hU E g hg r hrLevel k p hp
      obtain ⟨t, ht, htLevel, hpt⟩ :=
        infiniteStrongPicture_next_relative_exists hU
          (g k) p hpU hpLevel
      obtain ⟨z, hz, _⟩ := relativeNextLayer_child_exists
        hU hf E (relativeCompletionLayers hU E g hg r k)
        (g k) (g (k + 1))
        (Nat.succ_le_of_lt (hg (Nat.lt_succ_self k)))
        p hp hpLevel t ht htLevel hpt
      exact ⟨z, hz⟩


end CoordNode
end ThreeUniformDiaries
