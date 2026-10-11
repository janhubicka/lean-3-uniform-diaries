import ThreeUniformDiaries.InfiniteStrongRelativeLevels
import ThreeUniformDiaries.ProtectedConeTruncations

/-!
# Protected cone choice wholly inside a selected strong coordinate U

The ambient protected completion uses zero extension when an
immediate child cone contains no future prescribed E-node.
Such a fallback can leave U. Instead, use the checked relative
pruning of U to choose a retained descendant at the next selected
relative level. Guided cones use the existing meet-closed
protectedGuide and the selected-ancestor closure inside U.

The resulting choice:
* belongs to U,
* lies on the required target ambient level f L,
* extends the prescribed retained child,
* stays below every future E-node in that cone when E avoids the
  open gap from f i to f L.

This is the local step required for strong completion INSIDE U.
The global layer iteration and geometric composition remain separate.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- A protected guide chosen from E lies inside the surrounding U
whenever E is a subset of U and the target level is selected in U. -/
theorem protectedGuide_mem_strong_picture
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E : Set CoordNode) (hEU : E ⊆ U)
    (t : CoordNode) (L : Nat)
    (hex : ∃ x ∈ E, t ≤ x ∧ f L ≤ level x) :
    protectedGuide E t (f L) hex ∈ U := by
  let x : CoordNode := Classical.choose hex
  have hxE : x ∈ E := (Classical.choose_spec hex).1
  have hxU : x ∈ U := hEU hxE
  obtain ⟨j, hxLevel⟩ := hU.selected_levels x hxU
  have hLx : f L ≤ level x := (Classical.choose_spec hex).2.2
  have hLj : L ≤ j := by
    by_contra hnot
    have hjL : j < L := Nat.lt_of_not_ge hnot
    have hstrict := hf hjL
    rw [hxLevel] at hLx
    omega
  change truncate x (f L) ∈ U
  exact infiniteStrongPicture_selected_truncate_mem
    hU hf hrootLevel L j hLj x hxU hxLevel

/-- Choose one U-node in a relative successor cone at relative
level L. An E-guided cone uses its protected future E-ancestor;
an empty one uses a genuine later descendant in U. -/
noncomputable def relativeProtectedChoice
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (i L : Nat) (hL : i + 1 ≤ L)
    (t : CoordNode) (ht : t ∈ U)
    (htLevel : level t = f (i + 1)) : CoordNode :=
  if hex : ∃ x ∈ E, t ≤ x ∧ f L ≤ level x then
    protectedGuide E t (f L) hex
  else
    Classical.choose
      (infiniteStrongPicture_later_relative_exists
        hU (i + 1) L hL t ht htLevel)

/-- The protected relative choice never leaves the strong ambient U. -/
theorem relativeProtectedChoice_mem
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E : Set CoordNode) (hEU : E ⊆ U)
    (i L : Nat) (hL : i + 1 ≤ L)
    (t : CoordNode) (ht : t ∈ U)
    (htLevel : level t = f (i + 1)) :
    relativeProtectedChoice hU E i L hL t ht htLevel ∈ U := by
  classical
  by_cases hex : ∃ x ∈ E, t ≤ x ∧ f L ≤ level x
  · simpa only [relativeProtectedChoice, dif_pos hex] using
      protectedGuide_mem_strong_picture
        hU hf hrootLevel E hEU t L hex
  · have hz :=
      (Classical.choose_spec
        (infiniteStrongPicture_later_relative_exists
          hU (i + 1) L hL t ht htLevel)).1
    simpa only [relativeProtectedChoice, dif_neg hex] using hz

/-- Every relative choice occupies the prescribed selected U-level. -/
theorem relativeProtectedChoice_level
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (i L : Nat) (hL : i + 1 ≤ L)
    (t : CoordNode) (ht : t ∈ U)
    (htLevel : level t = f (i + 1)) :
    level (relativeProtectedChoice hU E i L hL t ht htLevel) =
      f L := by
  classical
  by_cases hex : ∃ x ∈ E, t ≤ x ∧ f L ≤ level x
  · simpa only [relativeProtectedChoice, dif_pos hex] using
      protectedGuide_level E t (f L) hex
  · have hz :=
      (Classical.choose_spec
        (infiniteStrongPicture_later_relative_exists
          hU (i + 1) L hL t ht htLevel)).2.1
    simpa only [relativeProtectedChoice, dif_neg hex] using hz

/-- The relative choice stays in the requested retained child cone. -/
theorem relativeProtectedChoice_extends
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f)
    (E : Set CoordNode)
    (i L : Nat) (hL : i + 1 ≤ L)
    (t : CoordNode) (ht : t ∈ U)
    (htLevel : level t = f (i + 1)) :
    t ≤ relativeProtectedChoice hU E i L hL t ht htLevel := by
  classical
  have htL : level t ≤ f L := by
    rw [htLevel]
    exact hf.monotone hL
  by_cases hex : ∃ x ∈ E, t ≤ x ∧ f L ≤ level x
  · simpa only [relativeProtectedChoice, dif_pos hex] using
      protectedGuide_extends E t (f L) htL hex
  · have hz :=
      (Classical.choose_spec
        (infiniteStrongPicture_later_relative_exists
          hU (i + 1) L hL t ht htLevel)).2.2
    simpa only [relativeProtectedChoice, dif_neg hex] using hz

/-- A future prescribed E-node remains above the protected relative
choice. Meet closure and the empty intervening E-level interval
make the guide independent of its particular witness. -/
theorem relativeProtectedChoice_below_prescribed
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f)
    (E : Set CoordNode) (hE : MeetClosed E)
    (i L : Nat) (hL : i + 1 ≤ L)
    (hgap : AvoidsOpenLevelGap E (f i) (f L))
    (t : CoordNode) (ht : t ∈ U)
    (htLevel : level t = f (i + 1))
    (x : CoordNode) (hx : x ∈ E)
    (htx : t ≤ x) (hxL : f L ≤ level x) :
    relativeProtectedChoice hU E i L hL t ht htLevel ≤ x := by
  have hlt : f i < level t := by
    rw [htLevel]
    exact hf (Nat.lt_succ_self i)
  have hex : ∃ y ∈ E, t ≤ y ∧ f L ≤ level y :=
    ⟨x, hx, htx, hxL⟩
  simpa only [relativeProtectedChoice, dif_pos hex] using
    (protectedGuide_below E hE (f i) (f L) hgap
      t x hlt hx htx hxL hex)

end CoordNode
end ThreeUniformDiaries
