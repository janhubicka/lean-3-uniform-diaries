import ThreeUniformDiaries.DiaryUniformOldStageTailColour

/-!
# Track D: cofinal finite mixed types have a coherent virtual limit

A sequence of candidate target vertices can realize finitely many
different COMPLETE mixed singleton type masks at each fixed target
cut B. One such mask recurs cofinally. More strongly, these recurrent
masks can be selected *coherently for every finite B at once*: the
mask at B+1 restricts to the chosen mask at B. Every selected mask
still occurs at arbitrarily late input indices.

For genuine finitely persistent diary stages, first stabilize the
COMPLETE new nonleaf generator profile. Choose one finite-horizon
witness at every horizon. The virtual-type construction applied to
the resulting sequence of new-leaf images supplies coherent mixed
masks across ALL finite target cuts while preserving that fixed
nonleaf record and the old supported image map.

There is NO claim that a single vertex of the prescribed target
leaf range realizes the full countable type. Countable coherent
finite-type data and realization by one actual target leaf are
distinct, even for sequences in an infinite target.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finite target-cut singleton colour which is attained at
arbitrarily late indices in the specified sequence v. -/
structure CofinalMixedColourState
    (K : Ordered3Graph Nat) (v : Nat → Nat) (B : Nat) where
  colour : Fin B → Fin B → Bool
  recurrent : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
    DiaryLowerBoundColors.singletonColour K B (v n) = colour

/-- At cut zero there is exactly one mixed type, and every vertex
realizes it. -/
private def cofinalMixedColourBase
    (K : Ordered3Graph Nat) (v : Nat → Nat) :
    CofinalMixedColourState K v 0 where
  colour := fun x => Fin.elim0 x
  recurrent := by
    intro N
    refine ⟨N, le_rfl, ?_⟩
    funext x
    exact Fin.elim0 x

/-- A cofinally recurring mixed colour at cut B has some
cofinally recurring extension at B+1. This uses FINITENESS of the
complete Boolean mask palette and does not assume realization
of a countable type. -/
private theorem cofinalMixedColour_next
    {K : Ordered3Graph Nat} {v : Nat → Nat} {B : Nat}
    (S : CofinalMixedColourState K v B) :
    ∃ T : CofinalMixedColourState K v (B + 1),
      ∀ (x y : Fin B),
        T.colour x.castSucc y.castSucc = S.colour x y := by
  classical
  let C := Fin (B + 1) → Fin (B + 1) → Bool
  let R : C → Nat → Prop := fun c N =>
    ∃ n : Nat, N ≤ n ∧
      DiaryLowerBoundColors.singletonColour K B (v n) = S.colour ∧
      DiaryLowerBoundColors.singletonColour K (B + 1) (v n) = c
  have hDown : ∀ (c : C) (n k : Nat),
      k ≤ n → R c n → R c k := by
    intro c n k hkn
    rintro ⟨t, hnt, hOld, hNew⟩
    exact ⟨t, hkn.trans hnt, hOld, hNew⟩
  have hCover : ∀ N : Nat, ∃ c : C,
      c ∈ (Finset.univ : Finset C) ∧ R c N := by
    intro N
    obtain ⟨n, hn, hOld⟩ := S.recurrent N
    exact ⟨DiaryLowerBoundColors.singletonColour K (B + 1) (v n),
      Finset.mem_univ _, n, hn, hOld, rfl⟩
  obtain ⟨c, _hc, hAll⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset C) R hDown hCover
  let T : CofinalMixedColourState K v (B + 1) := {
    colour := c
    recurrent := by
      intro N
      obtain ⟨n, hn, _hOld, hNew⟩ := hAll N
      exact ⟨n, hn, hNew⟩
  }
  refine ⟨T, ?_⟩
  intro x y
  obtain ⟨n, _hn, hOld, hNew⟩ := hAll 0
  change c x.castSucc y.castSucc = S.colour x y
  calc
    c x.castSucc y.castSucc =
        DiaryLowerBoundColors.singletonColour K (B + 1) (v n)
          x.castSucc y.castSucc :=
      (congrFun (congrFun hNew x.castSucc) y.castSucc).symm
    _ = DiaryLowerBoundColors.singletonColour K B (v n) x y := by
      simp [DiaryLowerBoundColors.singletonColour]
    _ = S.colour x y := congrFun (congrFun hOld x) y

/-- Canonical (classically selected) coherent succession of
cofinally recurring finite colours. No target vertex is selected
to realize the complete infinite family. -/
private noncomputable def cofinalMixedColourStates
    (K : Ordered3Graph Nat) (v : Nat → Nat) :
    (B : Nat) → CofinalMixedColourState K v B :=
  Nat.rec (cofinalMixedColourBase K v)
    (fun _ S => Classical.choose (cofinalMixedColour_next S))

/-- The selected complete finite mixed type at B+1 literally
restricts to the type selected at B. -/
private theorem cofinalMixedColourStates_project
    (K : Ordered3Graph Nat) (v : Nat → Nat)
    (B : Nat) (x y : Fin B) :
    (cofinalMixedColourStates K v (B + 1)).colour
        x.castSucc y.castSucc =
      (cofinalMixedColourStates K v B).colour x y := by
  exact (Classical.choose_spec
    (cofinalMixedColour_next (cofinalMixedColourStates K v B))) x y

/-- Every sequence of target vertices has a coherent countable
VIRTUAL mixed singleton type: one finite Boolean mask per numerical
cut, with literal restriction coherence and cofinal realizability of
every finite cut. It may have NO realizing target vertex. -/
theorem exists_coherent_cofinal_mixed_singleton_type
    (K : Ordered3Graph Nat) (v : Nat → Nat) :
    ∃ c : (B : Nat) → Fin B → Fin B → Bool,
      (∀ (B : Nat) (x y : Fin B),
        c (B + 1) x.castSucc y.castSucc = c B x y) ∧
      (∀ (B N : Nat), ∃ n : Nat, N ≤ n ∧
        DiaryLowerBoundColors.singletonColour K B (v n) = c B) := by
  refine ⟨fun B => (cofinalMixedColourStates K v B).colour, ?_, ?_⟩
  · intro B x y
    exact cofinalMixedColourStates_project K v B x y
  · intro B N
    exact (cofinalMixedColourStates K v B).recurrent N

/-- At a genuine new source leaf, a finitely persistent old
reserved stage has ONE nonleaf split-generator image record and
ONE compatible family of complete mixed singleton types over
EVERY finite target cut, each realized at arbitrarily long finite
source horizons.

The full type is *virtual*: the horizon witnesses g_n may have
different new-leaf target images, and nothing ensures that any
single target leaf realizes all finite masks. -/
theorem persistent_stage_has_coherent_virtual_mixed_leaf_type
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (P : PersistentReservedDiaryStage H K F m f) :
    ∃ p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat),
      ∃ c : (B : Nat) → Fin B → Fin B → Bool,
        (∀ (B : Nat) (x y : Fin B),
          c (B + 1) x.castSucc y.castSucc = c B x y) ∧
        (∀ (B N : Nat), ∃ n : Nat, N ≤ n ∧
          ∃ g : Nat → Nat,
            ReservedDiaryStage H K F (m + 1 + n) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
              g u.val = p u) ∧
            DiaryLowerBoundColors.singletonColour K B (g m) = c B) := by
  classical
  obtain ⟨p, hProfiles⟩ :=
    persistent_stage_has_stable_new_nonleaf_record hm P
  let g : Nat → (Nat → Nat) := fun n => Classical.choose (hProfiles n)
  have hg (n : Nat) :
      ReservedDiaryStage H K F (m + 1 + n) (g n) ∧
      CofinalDiaryStageCompatible H m f (g n) ∧
      (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
        g n u.val = p u) := by
    exact Classical.choose_spec (hProfiles n)
  let v : Nat → Nat := fun n => g n m
  obtain ⟨c, hCoherent, hRecur⟩ :=
    exists_coherent_cofinal_mixed_singleton_type K v
  refine ⟨p, c, hCoherent, ?_⟩
  intro B N
  obtain ⟨n, hn, hColour⟩ := hRecur B N
  obtain ⟨hQ, hOld, hProfile⟩ := hg n
  exact ⟨n, hn, g n, hQ, hOld, hProfile, hColour⟩

/-- Even fixing the entire virtual mixed type and the nonleaf
image record, every requested finite horizon and every target
cut admit a compatible realization of the corresponding finite
type. This is an exact-horizon form, obtained by restriction. -/
theorem persistent_stage_virtual_type_at_every_horizon
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (P : PersistentReservedDiaryStage H K F m f) :
    ∃ p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat),
      ∃ c : (B : Nat) → Fin B → Fin B → Bool,
        (∀ (B : Nat) (x y : Fin B),
          c (B + 1) x.castSucc y.castSucc = c B x y) ∧
        (∀ (B N : Nat), ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + N) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
            g u.val = p u) ∧
          DiaryLowerBoundColors.singletonColour K B (g m) = c B) := by
  obtain ⟨p, c, hCoherent, hEvery⟩ :=
    persistent_stage_has_coherent_virtual_mixed_leaf_type hm P
  refine ⟨p, c, hCoherent, ?_⟩
  intro B N
  obtain ⟨n, hn, g, Q, hOld, hProfile, hColour⟩ := hEvery B N
  exact ⟨g, Q.restrict (by omega), hOld, hProfile, hColour⟩

end DiaryLeafPriority
end ThreeUniformDiaries
