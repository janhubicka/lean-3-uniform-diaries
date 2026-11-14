import ThreeUniformDiaries.DiaryFixedOldSupportCofinalFiniteHorizon
import ThreeUniformDiaries.DiaryFiniteCandidatePersistentFusion

/-!
# Track D: the exact old-support compactness/escape dichotomy

A FIXED complete old reserved support map survives all later finite
source horizons if and only if genuine later reserved stages with
ALL earlier selected-leaf images bounded by ONE numerical B occur
at cofinally many horizons. This is a finite-palette statement:
the old selected-leaf image vector is finite, and every old S1/S2
generator image is forced by that vector.

Without a common bound on old selected leaves, the finite-choice
argument cannot be applied. Negating the equivalence gives a sharp
horizon escape theorem: if NO finitely persistent old support exists,
then at ALL sufficiently large horizons EVERY real reserved stage
has at least one earlier selected leaf image above any given B.

Independent finite-stage existence in full diaries makes this escape
NONVACUOUS. Combining it with the verified horizon-q fixed-old-support
recurrence theorem gives, in that escape case, a chosen arbitrarily
late horizon q and ONE large old support f_q with cofinally high
genuine q-horizon new-leaf images.

This is NOT a proof that the escape alternative is impossible, nor
a countable diary embedding, source-independent f, persistent new
leaf image, or the printed diary-unavoidability theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A single numerical B bounds the target images of ALL previously
selected source leaves in actual reserved finite-stage witnesses
through cofinally many later source horizons. The witnesses are
not required to agree with one another. -/
def HasCofinalBoundedOldLeafImages
    (H K : Ordered3Graph Nat) (F : Nat → Nat) (m : Nat) : Prop :=
  ∃ B : Nat, ∀ N : Nat,
    ∃ n : Nat, N ≤ n ∧
      ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + n) g ∧
        ∀ a : Nat, a ∈ countableDiaryLeafPrefix H m → g a ≤ B

/-- Exact old-support persistence criterion. An old stage is
finitely persistent IFF ONE bound controls ALL earlier selected-leaf
images along cofinally many genuine future finite stages.

In the nontrivial direction stabilize the finite whole vector
on L_m, select an actual later reserved stage, restrict to S_m,
and use checked S1/S2 support determinacy to obtain an old map
literally compatible with witnesses at every requested horizon.

No universal/generic leaf hypothesis is used: the result is
pure finite-image compactness inside actual reserved stages. -/
theorem persistentOldSupport_iff_cofinalBoundedOldLeafImages
    (H K : Ordered3Graph Nat) (F : Nat → Nat) (m : Nat) :
    (∃ f : Nat → Nat, PersistentReservedDiaryStage H K F m f) ↔
      HasCofinalBoundedOldLeafImages H K F m := by
  classical
  constructor
  · rintro ⟨f, Pf⟩
    let L := countableDiaryLeafPrefix H m
    let B := L.sup f
    refine ⟨B, ?_⟩
    intro N
    obtain ⟨g, Q, hKeep⟩ := Pf.2 N
    refine ⟨N, le_rfl, g, Q, ?_⟩
    intro a ha
    have haSupport : a ∈ countableDiaryFiniteSupport H m :=
      mem_finiteLeafMeetSupport_leaf H L a ha
    have hBound : f a ≤ B := Finset.le_sup (f := f) ha
    rw [hKeep a haSupport]
    exact hBound
  · rintro ⟨B, hRec⟩
    let L := countableDiaryLeafPrefix H m
    let Good : (Nat → Nat) → Nat → Prop := fun g n =>
      ReservedDiaryStage H K F (m + n) g
    have hAll : ∀ M : Nat,
        ∃ v : Nat, ∃ g : Nat → Nat,
          M < v ∧ Good g v ∧
          ∀ a : Nat, a ∈ L → g a ≤ B := by
      intro M
      obtain ⟨n, hN, g, Q, hOldBound⟩ := hRec (M + 1)
      exact ⟨n, g, by omega, Q, hOldBound⟩
    obtain ⟨v₀, g₀, hStage₀, hCofinal⟩ :=
      cofinal_bounded_finite_set_profile_stabilizes
        L B Good hAll
    have P₀ : ReservedDiaryStage H K F m g₀ :=
      hStage₀.restrict (by omega)
    refine ⟨g₀, P₀, ?_⟩
    intro n
    obtain ⟨v, g, hvn, Q, hSameLeaves⟩ := hCofinal n
    have Qn : ReservedDiaryStage H K F (m + n) g :=
      Q.restrict (by omega)
    have Qm : AdmissibleCofinalDiaryStage H K F m g :=
      Qn.1.restrict (by omega)
    have hKeep : CofinalDiaryStageCompatible H m g₀ g := by
      intro x hx
      exact (P₀.1.eq_on_support_of_selected_leaves Qm
        (fun a ha => (hSameLeaves a ha).symm) x hx).symm
    exact ⟨g, Qn, hKeep⟩

/-- Failure of old-support persistence means literal eventual
escape of SOME previous selected-leaf image in EVERY genuine
later stage. The quantifier is:
  for every B there exists N, and for ALL n≥N and ALL
  reserved S_(m+n) stages g, SOME selected old a has g(a)>B.

The statement may be vacuous without finite-stage existence;
the following full-diary corollary supplies that separately. -/
theorem noPersistentOldSupport_iff_eventualOldLeafEscape
    (H K : Ordered3Graph Nat) (F : Nat → Nat) (m : Nat) :
    (¬ ∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K F m f) ↔
      (∀ B : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + n) g →
          ∃ a : Nat, a ∈ countableDiaryLeafPrefix H m ∧ B < g a) := by
  classical
  constructor
  · intro hNo B
    by_contra hNoEscape
    have hBounded : HasCofinalBoundedOldLeafImages H K F m := by
      refine ⟨B, ?_⟩
      intro N
      by_contra hNoWitness
      apply hNoEscape
      refine ⟨N, ?_⟩
      intro n hn g Q
      by_contra hNoBig
      apply hNoWitness
      refine ⟨n, hn, g, Q, ?_⟩
      intro a ha
      by_contra hNotBounded
      have hBig : B < g a := by omega
      exact hNoBig ⟨a, ha, hBig⟩
    exact hNo
      ((persistentOldSupport_iff_cofinalBoundedOldLeafImages
        H K F m).mpr hBounded)
  · intro hEscape hPersistent
    obtain ⟨B, hBounded⟩ :=
      (persistentOldSupport_iff_cofinalBoundedOldLeafImages
        H K F m).mp hPersistent
    obtain ⟨N, hTail⟩ := hEscape B
    obtain ⟨n, hn, g, Q, hSmall⟩ := hBounded N
    obtain ⟨a, ha, hLarge⟩ := hTail n hn g Q
    have hOldSmall := hSmall a ha
    omega

/-- In genuine full source/target diaries, independently certified
finite reserved stages exist at EVERY source horizon inside the
original unordered induced generic target leaf range.

Thus either one old support is finitely persistent, or else ALL
sufficiently late genuine horizon stages must move at least one
old selected leaf beyond every fixed target bound B, and each such
horizon still has a real nonempty family of reserved stages.

No coherent family in the escaping branch is asserted. -/
theorem RoleDiary.persistent_old_support_or_nonvacuous_old_leaf_escape
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) :
    (∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K (fun t : Nat => F t) m f) ∨
    (∀ B : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
      (∃ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) (m + n) g) ∧
      (∀ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) (m + n) g →
        ∃ a : Nat, a ∈ countableDiaryLeafPrefix H m ∧ B < g a)) := by
  classical
  by_cases hPersist :
      ∃ f : Nat → Nat,
        PersistentReservedDiaryStage H K (fun t : Nat => F t) m f
  · exact Or.inl hPersist
  · right
    have hEsc :=
      (noPersistentOldSupport_iff_eventualOldLeafEscape
        H K (fun t : Nat => F t) m).mp hPersist
    have hUniversal : Ordered3Graph.CountablyUniversal G.graph := by
      intro A
      obtain ⟨v, hMono, hInduced⟩ :=
        G.exists_countable_induced_embedding A
      let e : Ordered3Graph.Embedding A G.graph := {
        toFun := v
        strictMono := hMono
        edge_iff := by
          intro a b c hab hbc
          exact hInduced a b c hab hbc
      }
      exact ⟨e.asUnordered⟩
    intro B
    obtain ⟨N, hTail⟩ := hEsc B
    refine ⟨N, ?_⟩
    intro n hn
    constructor
    · exact exists_independent_reserved_stage_in_universal_leaf_range
        DH DK G hUniversal F hFLeaf (m + n)
    · exact hTail n hn

/-- Strengthened fixed-horizon consequence in the escape branch:
assuming NO persistent old S_m support, each bound B forces
a sufficiently late q≥m+1 at which ALL genuine reserved q-stages
move some old leaf above B, YET a NEWLY selected complete old
support f_q with one old image >B admits cofinally high
genuine q-stage new-leaf successors inside the ORIGINAL F range.

The support f_q may depend on B and q. This does not rule out
the escaping alternative or construct a persistent new image. -/
theorem RoleDiary.exists_cofinal_horizon_with_forced_old_leaf_drift
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hOldNonempty : (countableDiaryLeafPrefix H m).Nonempty)
    (hNoPersistent : ¬ ∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K (fun t : Nat => F t) m f) :
    ∀ B : Nat, ∃ q : Nat, m + 1 ≤ q ∧
      (∀ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) q g →
        ∃ a : Nat, a ∈ countableDiaryLeafPrefix H m ∧ B < g a) ∧
      ∃ f : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
        (∃ a : Nat, a ∈ countableDiaryLeafPrefix H m ∧ B < f a) ∧
        (∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
          M < F t ∧
          ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m = F t) := by
  classical
  have hEscape :=
    (noPersistentOldSupport_iff_eventualOldLeafEscape
      H K (fun t : Nat => F t) m).mp hNoPersistent
  intro B
  obtain ⟨N, hTail⟩ := hEscape B
  let n := max 1 N
  let q := m + n
  have hNn : N ≤ n := le_max_right 1 N
  have hmq : m + 1 ≤ q := by
    dsimp [q, n]
    omega
  have hDrift : ∀ g : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) q g →
      ∃ a : Nat, a ∈ countableDiaryLeafPrefix H m ∧ B < g a := by
    intro g Q
    exact hTail n hNn g Q
  obtain ⟨f, Pf, hRec⟩ :=
    DH.exists_some_fixed_old_support_with_unbounded_new_leaf_at_horizon
      DK G F hFLeaf m q hmq hm hOldNonempty
  have hOldLarge :
      ∃ a : Nat, a ∈ countableDiaryLeafPrefix H m ∧ B < f a := by
    obtain ⟨t, g, _hHigh, Q, hKeep, _hNew⟩ := hRec 0
    obtain ⟨a, ha, hBig⟩ := hDrift g Q
    have haSupport : a ∈ countableDiaryFiniteSupport H m :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H m) a ha
    rw [hKeep a haSupport] at hBig
    exact ⟨a, ha, hBig⟩
  exact ⟨q, hmq, hDrift, f, Pf, hOldLarge, hRec⟩

end DiaryLeafPriority
end ThreeUniformDiaries
