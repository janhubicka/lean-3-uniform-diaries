import ThreeUniformDiaries.RelativeCompletionPrefix
import ThreeUniformDiaries.InfiniteStrongRelativeSiblingMeets

/-!
# Meet closure of the protected relative completion INSIDE U

The protected completed layers are finite, lie within U, and retain
all prescribed nodes. This file proves their union through any finite
index is closed under the *ambient* coordinate meet.

The induction follows the three cases: an old and a new node,
two descendants of distinct previous parents, and two descendants
of the same parent. The latter requires the genuine relative sibling
meet theorem because U's immediate child cones can skip arbitrary
ambient levels.

The resulting finite prefixes are now true meet-closed relative
strong pictures; the next step is to export a complete finite or
infinite strong-completion existence theorem and composition coding.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The ambient selected level of a completed prefix node determines
exactly its source layer index, since both f and the relative
selection sigma are strictly increasing. -/
theorem relativeCompletionPrefix_on_layer
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f)
    (E : Set CoordNode)
    (sigma : Nat → Nat) (hsigma : StrictMono sigma)
    (r : CoordNode) (hrLevel : level r = f (sigma 0))
    (i k : Nat) (hik : i ≤ k)
    (z : CoordNode)
    (hz : z ∈ relativeCompletionPrefix hU E sigma hsigma r k)
    (hzLevel : level z = f (sigma i)) :
    z ∈ relativeCompletionLayers hU E sigma hsigma r i := by
  rcases hz with ⟨j, hjk, hzj⟩
  have hjLevel : level z = f (sigma j) :=
    relativeCompletionLayers_level hU E sigma hsigma r
      hrLevel j z hzj
  have hEq : sigma j = sigma i :=
    hf.injective (hjLevel.symm.trans hzLevel)
  have hji : j = i := hsigma.injective hEq
  subst j
  exact hzj

/-- Every finite prefix of the relative protected completion is
closed under exact ambient meets, even across skipped U-levels.
No meet-closure property of E is needed for this structural fact. -/
theorem relativeCompletionPrefix_meetClosed
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E : Set CoordNode) (hEU : E ⊆ U)
    (sigma : Nat → Nat) (hsigma : StrictMono sigma)
    (r : CoordNode) (hr : r ∈ U)
    (hrLevel : level r = f (sigma 0))
    (k : Nat) :
    MeetClosed (relativeCompletionPrefix hU E sigma hsigma r k) := by
  induction k with
  | zero =>
      intro x y hx hy
      rcases hx with ⟨i, hi, hx⟩
      rcases hy with ⟨j, hj, hy⟩
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst i
      subst j
      change x ∈ ({r} : Set CoordNode) at hx
      change y ∈ ({r} : Set CoordNode) at hy
      have hxEq : x = r := by simpa using hx
      have hyEq : y = r := by simpa using hy
      subst x
      subst y
      exact ⟨0, le_rfl, by
        change meet r r ∈ ({r} : Set CoordNode)
        simpa only [meet_self, Set.mem_singleton_iff]⟩
  | succ k ih =>
      let old := relativeCompletionPrefix hU E sigma hsigma r k
      let P := relativeCompletionLayers hU E sigma hsigma r k
      let L := sigma (k + 1)
      let hL : sigma k + 1 ≤ L :=
        Nat.succ_le_of_lt (hsigma (Nat.lt_succ_self k))
      have hLift : old ⊆
          relativeCompletionPrefix hU E sigma hsigma r (k + 1) :=
        relativeCompletionPrefix_mono hU E sigma hsigma
          r k (k + 1) (Nat.le_succ k)
      have hPold : P ⊆ old := by
        intro p hp
        exact ⟨k, le_rfl, hp⟩
      intro x y hx hy
      have hxs := (relativeCompletionPrefix_succ_iff
        hU E sigma hsigma r k x).mp hx
      have hys := (relativeCompletionPrefix_succ_iff
        hU E sigma hsigma r k y).mp hy
      rcases hxs with hxOld | hxNew
      · rcases hys with hyOld | hyNew
        · exact hLift (ih hxOld hyOld)
        · obtain ⟨p, hp, hpy⟩ :=
            relativeCompletionLayers_has_parent hU hf E
              sigma hsigma r k y hyNew
          have hxp : level x ≤ level p := by
            calc
              level x ≤ f (sigma k) :=
                relativeCompletionPrefix_level_le hU hf E
                  sigma hsigma r hrLevel k x hxOld
              _ = level p :=
                (relativeCompletionLayers_level hU E sigma hsigma
                  r hrLevel k p hp).symm
          have hc : ∃ c : CoordNode, c ≤ p ∧ c ≤ x :=
            ⟨r,
              relativeCompletionLayers_root_le hU hf E
                sigma hsigma r k p hp,
              relativeCompletionPrefix_root_le hU hf E
                sigma hsigma r k x hxOld⟩
          have hm : meet x y = meet x p :=
            meet_extension_right x p y hpy hxp hc
          rw [hm]
          exact hLift (ih hxOld (hPold hp))
      · rcases hys with hyOld | hyNew
        · obtain ⟨p, hp, hpx⟩ :=
            relativeCompletionLayers_has_parent hU hf E
              sigma hsigma r k x hxNew
          have hyp : level y ≤ level p := by
            calc
              level y ≤ f (sigma k) :=
                relativeCompletionPrefix_level_le hU hf E
                  sigma hsigma r hrLevel k y hyOld
              _ = level p :=
                (relativeCompletionLayers_level hU E sigma hsigma
                  r hrLevel k p hp).symm
          have hc : ∃ c : CoordNode, c ≤ p ∧ c ≤ y :=
            ⟨r,
              relativeCompletionLayers_root_le hU hf E
                sigma hsigma r k p hp,
              relativeCompletionPrefix_root_le hU hf E
                sigma hsigma r k y hyOld⟩
          have hm : meet x y = meet p y :=
            meet_extension_left p x y hpx hyp hc
          rw [hm]
          exact hLift (ih (hPold hp) hyOld)
        · change x ∈ relativeNextLayer hU E P
            (sigma k) L hL at hxNew
          change y ∈ relativeNextLayer hU E P
            (sigma k) L hL at hyNew
          rcases hxNew with ⟨a, rfl⟩
          rcases hyNew with ⟨b, rfl⟩
          change meet (a.chosen hU E L hL)
              (b.chosen hU E L hL) ∈
            relativeCompletionPrefix hU E sigma hsigma r (k + 1)
          have haParent : a.parent ≤ a.chosen hU E L hL :=
            a.parent_le_chosen hU hf E L hL
          have hbParent : b.parent ≤ b.chosen hU E L hL :=
            b.parent_le_chosen hU hf E L hL
          by_cases hpar : a.parent = b.parent
          · by_cases hchild : a.child = b.child
            · obtain ⟨z, hz, hunique⟩ :=
                relativeNextLayer_unique_child hU hf E P
                  (sigma k) L hL a.parent a.parent_mem
                  a.parent_level a.child a.child_mem
                  a.child_level a.parent_le_child
              have haMem : a.chosen hU E L hL ∈
                  relativeNextLayer hU E P (sigma k) L hL ∧
                    a.child ≤ a.chosen hU E L hL :=
                ⟨⟨a, rfl⟩, a.child_le_chosen hU hf E L hL⟩
              have hbMem : b.chosen hU E L hL ∈
                  relativeNextLayer hU E P (sigma k) L hL ∧
                    a.child ≤ b.chosen hU E L hL := by
                refine ⟨⟨b, rfl⟩, ?_⟩
                rw [hchild]
                exact b.child_le_chosen hU hf E L hL
              have haEq : a.chosen hU E L hL = z :=
                hunique _ haMem
              have hbEq : b.chosen hU E L hL = z :=
                hunique _ hbMem
              rw [haEq, hbEq, meet_self]
              exact ⟨k + 1, le_rfl, hz.1⟩
            · have hpU : a.parent ∈ U :=
                (relativeCompletionLayers_subset hU hf hrootLevel
                  E hEU sigma hsigma r hr k) a.parent_mem
              have hbChildParent : a.parent ≤ b.child := by
                rw [hpar]
                exact b.parent_le_child
              have hm : meet (a.chosen hU E L hL)
                  (b.chosen hU E L hL) = a.parent :=
                infiniteStrongPicture_relative_sibling_descendant_meet
                  hU hf (sigma k)
                  a.parent a.child b.child
                  (a.chosen hU E L hL) (b.chosen hU E L hL)
                  hpU a.child_mem b.child_mem
                  a.parent_level a.child_level b.child_level
                  a.parent_le_child hbChildParent hchild
                  (a.child_le_chosen hU hf E L hL)
                  (b.child_le_chosen hU hf E L hL)
              rw [hm]
              exact hLift (hPold a.parent_mem)
          · have hsameLevel : level a.parent = level b.parent :=
              a.parent_level.trans b.parent_level.symm
            have hc : ∃ c : CoordNode,
                c ≤ a.parent ∧ c ≤ b.parent :=
              ⟨r,
                relativeCompletionLayers_root_le hU hf E
                  sigma hsigma r k a.parent a.parent_mem,
                relativeCompletionLayers_root_le hU hf E
                  sigma hsigma r k b.parent b.parent_mem⟩
            have hm :=
              meet_descendants_distinct_parents
                a.parent b.parent
                (a.chosen hU E L hL) (b.chosen hU E L hL)
                hsameLevel hpar haParent hbParent hc
            rw [hm]
            exact hLift (ih (hPold a.parent_mem) (hPold b.parent_mem))

end CoordNode
end ThreeUniformDiaries
