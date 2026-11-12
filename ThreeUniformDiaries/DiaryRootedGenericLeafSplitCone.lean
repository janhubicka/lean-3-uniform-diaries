import ThreeUniformDiaries.DiaryGenericMixedConeIndivisibility
import ThreeUniformDiaries.DiarySingletonColourCofinalCone
import ThreeUniformDiaries.DiaryTwoLeafMarkerOrientation

/-!
# Track D: a genuine GENERIC leaf subcopy in one rooted E2 split fibre

Let F be an unordered induced embedding of the actual enumerated generic
3-uniform hypergraph G into the genuine leaves of a full target diary K.
Fix ANY target leaf w, including an old already selected leaf.

Colour each vertex n of G by:
* the exact numerical singleton meet oneMeet_K(w,F(n)), a FINITE
  integer in [0,w], including the capped self-meet case; and
* the Boolean test max(B,w) < F(n).

The kernel-verified finite vertex-colouring ATR theorem yields an
induced generic selfcopy of G with one CONSTANT colour. Because F and
the self-embedding are injective, their composite has numerically
unbounded images. Therefore the winning Boolean bit is TRUE. The
common meet is a genuine one-split s<w (not the capped self-leaf).

Now use a second finite-palette/downward-recurrence argument over
the FINITE possible values s<w: one s supports an induced generic
selfcopy with the SAME exact root meet s beyond EVERY finite target
bound B. The selfcopies may vary with B and are NOT assumed coherent.

Unlike an arbitrary infinite E2 tail, this witnesses FULL induced
leaf-only generic E5 triple patterns in each chosen rooted fibre.
The winning s remains existential: no source-required E2 polarity,
numerical gap placement, or old-support finite-horizon persistence
is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any injected unordered GENERIC leaf copy contains a genuine
induced generic selfcopy above any bound B, on which the exact
singleton meet with a FIXED target leaf w is constant at one
genuine one-split s<w.

The embedding u is in the SOURCE generic G, so the resulting
target leaf map F ∘ u is automatically an unordered induced generic
subcopy of K in the ORIGINAL prescribed leaf range. -/
theorem RoleDiary.exists_generic_rooted_split_subcopy_above
    {K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (w : Nat) (hwLeaf : IsLeaf K w) (B : Nat) :
    ∃ s : Nat,
      IsOneSplit K s ∧ s < w ∧
      ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
        u.AuxTypeRespecting ∧
        ∀ t : Nat,
          B < F (u t) ∧
          K.oneMeetLevel w (F (u t)) = s := by
  classical
  let C : Type := (Fin (w + 1) × Bool)
  letI : Nonempty C :=
    ⟨((⟨0, by omega⟩ : Fin (w + 1)), false)⟩
  let χ : Nat → C := fun n =>
    ((⟨K.oneMeetLevel w (F n), by
      have hCap := K.oneMeetLevel_le_min w (F n)
      omega⟩ : Fin (w + 1)),
      decide (max B w < F n))
  obtain ⟨u,hu,p,hMono⟩ :=
    generic_finite_vertex_colouring_monochromatic G χ
  have hFInjective : Function.Injective (fun n : Nat => F (u n)) :=
    F.injective.comp u.strictMono.injective
  obtain ⟨N,hEventually⟩ :=
    injective_nat_eventually_above_bound
      (fun n : Nat => F (u n)) hFInjective (max B w)
  have hAtN : decide (max B w < F (u N)) = p.2 := by
    have h := congrArg (fun z : C => z.2) (hMono N)
    change decide (max B w < F (u N)) = p.2 at h
    exact h
  have hpTrue : p.2 = true := by
    have hYes : decide (max B w < F (u N)) = true := by
      simp [hEventually N (le_refl N)]
    exact hAtN.symm.trans hYes
  have hHigh (t : Nat) : max B w < F (u t) := by
    have hAt : decide (max B w < F (u t)) = p.2 := by
      have h := congrArg (fun z : C => z.2) (hMono t)
      change decide (max B w < F (u t)) = p.2 at h
      exact h
    have hDec : decide (max B w < F (u t)) = true :=
      hAt.trans hpTrue
    by_cases hPos : max B w < F (u t)
    · exact hPos
    · simp [hPos] at hDec
  let s := p.1.val
  have hMeet (t : Nat) :
      K.oneMeetLevel w (F (u t)) = s := by
    have h := congrArg (fun z : C => z.1.val) (hMono t)
    change K.oneMeetLevel w (F (u t)) = p.1.val at h
    exact h
  have hDistinct : w ≠ F (u 0) :=
    ne_of_lt (lt_of_le_of_lt (le_max_right B w) (hHigh 0))
  have hsRole : IsOneSplit K s := by
    have h :=
      DK.singleton_meets w (F (u 0))
        hwLeaf (hFLeaf (u 0)) hDistinct
    rw [hMeet 0] at h
    exact h
  have hsBelow : s < w := by
    have h :=
      DK.oneMeet_lt_left_of_distinct_leaves
        w (F (u 0)) hwLeaf (hFLeaf (u 0)) hDistinct
    rw [hMeet 0] at h
    exact h
  refine ⟨s,hsRole,hsBelow,u,hu,?_⟩
  intro t
  exact ⟨lt_of_le_of_lt (le_max_left B w) (hHigh t),
    hMeet t⟩

/-- Fix ANY genuine target leaf w and an actual unordered induced
generic leaf copy F[G]. There is ONE genuine target one-split s<w
that works at ALL numerical bounds B: at each B, the original
F-range contains an induced generic source selfcopy whose every
leaf is >B and has exact singleton meet s with w.

One s is chosen uniformly for all B by finite-choice persistence
on the finite set of splits <w; the generic selfcopies themselves
need NOT be compatible. Their images preserve all generic leaf-only
E5 triples because F is an UNORDERED induced embedding.

This does not force the chosen s to satisfy the prescribed SOURCE
E2 orientation or old split/leaf spacing constraints. -/
theorem RoleDiary.exists_one_root_split_with_generic_subcopies_all_bounds
    {K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (w : Nat) (hwLeaf : IsLeaf K w) :
    ∃ s : Nat,
      IsOneSplit K s ∧ s < w ∧
      (∀ B : Nat,
        ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
          u.AuxTypeRespecting ∧
          ∀ t : Nat,
            B < F (u t) ∧
            K.oneMeetLevel w (F (u t)) = s) := by
  classical
  let R : Nat → Nat → Prop := fun s B =>
    ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
      u.AuxTypeRespecting ∧
      ∀ t : Nat,
        B < F (u t) ∧
        K.oneMeetLevel w (F (u t)) = s
  have hDown : ∀ s B M : Nat,
      M ≤ B → R s B → R s M := by
    intro s B M hMB
    rintro ⟨u,hu,hAll⟩
    refine ⟨u,hu,?_⟩
    intro t
    obtain ⟨hHigh,hMeet⟩ := hAll t
    exact ⟨lt_of_le_of_lt hMB hHigh,hMeet⟩
  have hCover : ∀ B : Nat,
      ∃ s : Nat, s ∈ Finset.range w ∧ R s B := by
    intro B
    obtain ⟨s,_hsRole,hsBelow,u,hu,hAll⟩ :=
      DK.exists_generic_rooted_split_subcopy_above
        G F hFLeaf w hwLeaf B
    exact ⟨s,Finset.mem_range.mpr hsBelow,u,hu,hAll⟩
  obtain ⟨s,hMem,hRecur⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.range w) R hDown hCover
  have hsBelow : s < w := Finset.mem_range.mp hMem
  have hsRole : IsOneSplit K s := by
    obtain ⟨u,_hu,hAll⟩ := hRecur w
    have hwLt : w < F (u 0) := (hAll 0).1
    have hOne :=
      DK.singleton_meets w (F (u 0))
        hwLeaf (hFLeaf (u 0)) (ne_of_lt hwLt)
    rw [(hAll 0).2] at hOne
    exact hOne
  exact ⟨s,hsRole,hsBelow,hRecur⟩

end DiaryLeafPriority
end ThreeUniformDiaries
