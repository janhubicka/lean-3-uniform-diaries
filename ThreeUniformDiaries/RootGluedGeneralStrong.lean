import ThreeUniformDiaries.RootGluedAmbientRank
import ThreeUniformDiaries.RootGluedStrongSuccessorCones
import ThreeUniformDiaries.InfiniteStrongSelectedAncestors
import Milliken.GeneralTree

/-!
# Genuine ATR strong vectors as Milliken.GeneralTree.StrongSubtree

The forward root-gluing proof gives intrinsic strongness in actual
E0/E1/E2 coordinate cones. We now convert those checked data to
Milliken's literal general-tree strong-subtree structure, not to
another abstractly equivalent or postulated type.

The nontrivial "no ghost nodes" predecessor field is obtained from
the proved selected-truncation closure of each real coordinate
strong picture, including skipped ambient levels.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Intrinsic glued ancestor order is exactly the order from
Mathlib's `WithBot`-rooted type forest. -/
theorem gluedLE_iff_le
    (x y : WithBot CoordNode) :
    gluedLE x y ↔ x ≤ y := by
  cases x with
  | bot =>
      cases y <;> simp [gluedLE]
  | coe a =>
      cases y with
      | bot =>
          simp [gluedLE, WithBot.not_coe_le_bot]
      | coe b =>
          change (a ≤ b) ↔
            ((a : WithBot CoordNode) ≤ (b : WithBot CoordNode))
          exact (WithBot.coe_le_coe (a := a) (b := b)).symm

/-- Every earlier selected ancestor of a node in a genuine strong
vector picture belongs to its literal glued carrier. -/
theorem gluedVectorStrongCarrier_truncate_mem
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (i j : Nat) (hij : i ≤ j)
    (z : CoordNode)
    (hz : some z ∈ gluedVectorStrongCarrier h₀ h₁ h₂)
    (hzlevel : level z = f j) :
    some (truncate z (f i)) ∈
      gluedVectorStrongCarrier h₀ h₁ h₂ := by
  cases z with
  | aux n a =>
      have hmem : CoordNode.aux n a ∈ S₂ :=
        (gluedVectorStrongCarrier_aux_iff h₀ h₁ h₂ n a).mp hz
      have htr :=
        infiniteStrongPicture_selected_truncate_mem
          h₂ hf rfl i j hij (.aux n a) hmem hzlevel
      change CoordNode.aux (f i) (a.truncate (f i)) ∈ S₂ at htr
      exact (gluedVectorStrongCarrier_aux_iff
        h₀ h₁ h₂ (f i) (a.truncate (f i))).mpr htr
  | one n a =>
      have hmem : CoordNode.one n a ∈ S₁ :=
        (gluedVectorStrongCarrier_one_iff h₀ h₁ h₂ n a).mp hz
      have htr :=
        infiniteStrongPicture_selected_truncate_mem
          h₁ hf rfl i j hij (.one n a) hmem hzlevel
      change CoordNode.one (f i) (a.truncate (f i)) ∈ S₁ at htr
      exact (gluedVectorStrongCarrier_one_iff
        h₀ h₁ h₂ (f i) (a.truncate (f i))).mpr htr
  | enum n a =>
      have hmem : CoordNode.enum n a ∈ S₀ :=
        (gluedVectorStrongCarrier_enum_iff h₀ h₁ h₂ n a).mp hz
      have htr :=
        infiniteStrongPicture_selected_truncate_mem
          h₀ hf rfl i j hij (.enum n a) hmem hzlevel
      change CoordNode.enum (f i) (a.truncate (f i)) ∈ S₀ at htr
      exact (gluedVectorStrongCarrier_enum_iff
        h₀ h₁ h₂ (f i) (a.truncate (f i))).mpr htr

/-- The actual scalar strong subtree required by lean-milliken,
constructed from synchronized E0/E1/E2 strong pictures. -/
noncomputable def gluedVectorStrong_to_milliken
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) :
    Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree := by
  let W : Set (WithBot CoordNode) :=
    gluedVectorStrongCarrier h₀ h₁ h₂
  have hW : RootedGluedInfiniteStrong W f :=
    gluedVectorStrongCarrier_strong h₀ h₁ h₂
  have hconvert :
      ∀ (n : Nat) (y z : WithBot CoordNode),
        (z ∈ W ∧
          gluedLevel z = gluedSelectedLevel f (n + 1) ∧
          gluedLE y z) ↔
        (z ∈ W ∧
          rootGluedAmbientTree.level z = gluedSelectedLevel f (n + 1) ∧
          y ≤ z) := by
    intro n y z
    constructor
    · rintro ⟨hz, hzl, hyz⟩
      exact ⟨hz, (rootGluedAmbient_level_eq_gluedLevel z).trans hzl,
        (gluedLE_iff_le y z).mp hyz⟩
    · rintro ⟨hz, hzl, hyz⟩
      exact ⟨hz, (rootGluedAmbient_level_eq_gluedLevel z).symm.trans hzl,
        (gluedLE_iff_le y z).mpr hyz⟩
  refine {
    carrier := W
    levels := gluedSelectedLevel f
    levels_strictMono := gluedSelectedLevel_strictMono f hf
    root := ⊥
    root_mem := hW.root_mem
    root_level := rootGluedAmbientTree.level_root
    root_below := by intro x hx; exact bot_le
    carrier_levels := ?_
    predecessor_exists := ?_
    successor_unique := ?_
  }
  · intro x hx
    rcases hW.selected_levels x hx with hroot | ⟨i, hi⟩
    · subst x
      exact ⟨0, rootGluedAmbientTree.level_root⟩
    · refine ⟨i + 1, ?_⟩
      have hlev := rootGluedAmbient_level_eq_gluedLevel (x : WithBot CoordNode)
      exact hlev.trans (by
        simpa only [gluedSelectedLevel_succ] using hi)
  · intro n z hz hzlevel
    cases n with
    | zero =>
        exact ⟨⊥, hW.root_mem, rootGluedAmbientTree.level_root,
          bot_le⟩
    | succ i =>
        cases z with
        | none =>
            change rootGluedAmbientTree.level
              (none : WithBot CoordNode) = f (i + 1) + 1 at hzlevel
            have hzero : gluedLevel (none : WithBot CoordNode) =
                f (i + 1) + 1 :=
              (rootGluedAmbient_level_eq_gluedLevel
                (none : WithBot CoordNode)).symm.trans hzlevel
            change (0 : Nat) = f (i + 1) + 1 at hzero
            omega
        | some z =>
            have hzlevel' : level z = f (i + 1) := by
              change rootGluedAmbientTree.level
                (z : WithBot CoordNode) = f (i + 1) + 1 at hzlevel
              have hrank := rootGluedAmbient_level_coe z
              omega
            let p : CoordNode := truncate z (f i)
            have hpMem : (p : WithBot CoordNode) ∈ W :=
              gluedVectorStrongCarrier_truncate_mem
                h₀ h₁ h₂ hf i (i + 1) (Nat.le_succ i)
                z hz hzlevel'
            have hpLevel :
                rootGluedAmbientTree.level (p : WithBot CoordNode) =
                  gluedSelectedLevel f (i + 1) := by
              rw [rootGluedAmbient_level_coe]
              simp only [p, level_truncate, gluedSelectedLevel_succ]
            have hpLe : (p : WithBot CoordNode) ≤ (z : WithBot CoordNode) :=
              WithBot.coe_le_coe.mpr
                (truncate_le z (by rw [hzlevel']; exact hf.monotone (Nat.le_succ i)))
            exact ⟨(p : WithBot CoordNode), hpMem, hpLevel, hpLe⟩
  · intro n x hx hxlevel y hxy
    have hchild : gluedChild x y :=
      (gluedChild_iff_covBy x y).mpr hxy
    cases n with
    | zero =>
        cases x with
        | none =>
            obtain ⟨z, hz, huniq⟩ := hW.root_child y hchild
            rcases hz with ⟨hzW, hzL, hzY⟩
            have hnew : z ∈ W ∧
                gluedLevel z = gluedSelectedLevel f (0 + 1) ∧
                gluedLE y z :=
              ⟨hzW, hzL, hzY⟩
            refine ⟨z, (hconvert 0 y z).mp hnew, ?_⟩
            intro w hw
            rcases (hconvert 0 y w).mpr hw with ⟨hwW, hwL, hwY⟩
            exact huniq w ⟨hwW, hwL, hwY⟩
        | some x =>
            have hpos := rootGluedAmbient_level_coe x
            change rootGluedAmbientTree.level
              (x : WithBot CoordNode) = 0 at hxlevel
            omega
    | succ i =>
        cases x with
        | none =>
            change rootGluedAmbientTree.level
              (none : WithBot CoordNode) = f i + 1 at hxlevel
            have hzero : gluedLevel (none : WithBot CoordNode) =
                f i + 1 :=
              (rootGluedAmbient_level_eq_gluedLevel
                (none : WithBot CoordNode)).symm.trans hxlevel
            change (0 : Nat) = f i + 1 at hzero
            omega
        | some x =>
            have hxlevel' :
                gluedLevel (x : WithBot CoordNode) = f i + 1 := by
              change rootGluedAmbientTree.level
                (x : WithBot CoordNode) = f i + 1 at hxlevel
              exact (rootGluedAmbient_level_eq_gluedLevel
                (x : WithBot CoordNode)).symm.trans hxlevel
            obtain ⟨z, hz, huniq⟩ :=
              hW.next_child i (x : WithBot CoordNode) hx hxlevel' y hchild
            rcases hz with ⟨hzW, hzL, hzY⟩
            have hnew : z ∈ W ∧
                gluedLevel z = gluedSelectedLevel f ((i + 1) + 1) ∧
                gluedLE y z :=
              ⟨hzW, hzL, hzY⟩
            refine ⟨z, (hconvert (i + 1) y z).mp hnew, ?_⟩
            intro w hw
            rcases (hconvert (i + 1) y w).mpr hw with ⟨hwW, hwL, hwY⟩
            exact huniq w ⟨hwW, hwL, hwY⟩

end CoordNode
end ThreeUniformDiaries
