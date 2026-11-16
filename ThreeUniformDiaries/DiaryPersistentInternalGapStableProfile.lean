import ThreeUniformDiaries.DiaryPersistentFiniteFutureSplitPattern
import ThreeUniformDiaries.DiaryFullNewGeneratorProfileStabilisation

/-!
# Track A: bounded internal old-image gaps have a STABLE joint finite image record

At a genuinely FINITELY PERSISTENT reserved source stage f, take
two already-supported source vertices x<y and ANY finite set T of
source positions strictly between them. Future horizons eventually
contain ALL of T; every real later reserved witness that fixes the
old f must map T strictly inside the FIXED target gap (f x,f y).

The complete T-image vector therefore has FINITELY many possibilities,
although the entire future supported diary map may have infinitely
many possibilities. Apply the checked finite-choice downward
compactness theorem to the finite type T -> Fin(f y + 1), using
GENUINE reserved witnesses at ALL source horizons.

It selects ONE vector p such that at EVERY later source horizon
there is an ACTUAL reserved witness fixing the whole old f and
ALL T images equal to this SAME p simultaneously. The vector p
preserves strict order, roles, induced E5 edges and nonedges in T.
Source leaves in T have p-values in the ORIGINAL F range.

CRITICAL: the newly selected source leaf m lies ABOVE the entire
old support S_m, so it need not lie between fixed old endpoints.
This bounded-gap stabilization does NOT force a persistent image
of m, give a persistent stage at the expanded source horizon,
or solve countable diary unavoidability.

English-first audit:
notes/track_a_internal_gap_joint_horizon_stabilisation_20261116.md
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A whole finite set T of future source positions STRICTLY inside
one old supported interval (x,y) admits a fixed, strictly increasing,
exact-role and induced-edge image table p:T->Fin(f(y)+1).

The SAME p is realized by genuine fully reserved finite-source
stages at EVERY horizon m+k+n, while ALL old supported images f
remain fixed literally. No restriction to particular split roles,
genericity of target F, or order preservation by F is required.

The outside-new-leaf image may vary with n, and the conclusion
does NOT assert finite persistence of an entire new source stage. -/
theorem PersistentReservedDiaryStage.exists_cofinally_fixed_internal_gap_profile
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DH : RoleDiary H)
    (P : PersistentReservedDiaryStage H K F m f)
    {x y : Nat}
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (T : Finset Nat)
    (hBetween : ∀ s : Nat, s ∈ T → x < s ∧ s < y) :
    ∃ k : Nat,
      ∃ p : ({s : Nat // s ∈ T} → Fin (f y + 1)),
        (∀ s : {s : Nat // s ∈ T},
          f x < (p s).val ∧ (p s).val < f y) ∧
        (∀ s t : {s : Nat // s ∈ T}, s.val < t.val →
          (p s).val < (p t).val) ∧
        (∀ s : {s : Nat // s ∈ T}, IsLeaf H s.val →
          IsLeaf K (p s).val) ∧
        (∀ s : {s : Nat // s ∈ T}, IsOneSplit H s.val →
          IsOneSplit K (p s).val) ∧
        (∀ s : {s : Nat // s ∈ T}, IsTwoSplit H s.val →
          IsTwoSplit K (p s).val) ∧
        (∀ s : {s : Nat // s ∈ T}, IsLeaf H s.val →
          ∃ i : Nat, (p s).val = F i) ∧
        (∀ a b c : {s : Nat // s ∈ T},
          a.val < b.val → b.val < c.val →
          (H.edge a.val b.val c.val ↔
            K.edge (p a).val (p b).val (p c).val)) ∧
        (∀ n : Nat, ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + k + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          (∀ s : {s : Nat // s ∈ T}, g s.val = (p s).val)) := by
  classical
  let V := {s : Nat // s ∈ T}
  let Profile := V → Fin (f y + 1)
  obtain ⟨k, hFull⟩ :=
    countableDiaryFiniteSupport_contains_finset DH T
  have hSupport (n : Nat) (s : V) :
      s.val ∈ countableDiaryFiniteSupport H (m + k + n) :=
    (countableDiaryFiniteSupport_mono H k (m + k + n)
      (by omega)) (hFull s.val s.property)
  have hOldSupport (n : Nat) {s : Nat}
      (hs : s ∈ countableDiaryFiniteSupport H m) :
      s ∈ countableDiaryFiniteSupport H (m + k + n) :=
    (countableDiaryFiniteSupport_mono H m (m + k + n)
      (by omega)) hs
  let R : Profile → Nat → Prop := fun p n =>
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + k + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      (∀ s : V, g s.val = (p s).val)
  have hDown : ∀ (p : Profile) (n r : Nat),
      r ≤ n → R p n → R p r := by
    intro p n r hr
    rintro ⟨g, Q, hOld, hValue⟩
    exact ⟨g, Q.restrict (by omega), hOld, hValue⟩
  have hCover : ∀ n : Nat,
      ∃ p : Profile, p ∈ (Finset.univ : Finset Profile) ∧ R p n := by
    intro n
    obtain ⟨g, Qraw, hOld⟩ := P.2 (k + n)
    have Q : ReservedDiaryStage H K F (m + k + n) g := by
      simpa only [Nat.add_assoc] using Qraw
    let p : Profile := fun s =>
      ⟨g s.val, by
        have hOrder : g s.val < g y :=
          Q.1.ordered s.val y (hSupport n s)
            (hOldSupport n hy) (hBetween s.val s.property).2
        have hFix : g y = f y := hOld y hy
        omega⟩
    refine ⟨p, Finset.mem_univ _, g, Q, hOld, ?_⟩
    intro s
    rfl
  obtain ⟨p, _hp, hAll⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset Profile) R hDown hCover
  obtain ⟨g₀, Q₀, hOld₀, hValue₀⟩ := hAll 0
  have Q₀Now : ReservedDiaryStage H K F (m + k) g₀ := by
    simpa only [Nat.add_zero] using Q₀
  have hAt (s : V) :
      s.val ∈ countableDiaryFiniteSupport H (m + k) := by
    simpa only [Nat.add_zero] using hSupport 0 s
  have hOldAt {s : Nat}
      (hs : s ∈ countableDiaryFiniteSupport H m) :
      s ∈ countableDiaryFiniteSupport H (m + k) := by
    simpa only [Nat.add_zero] using hOldSupport 0 hs
  have hFixX : g₀ x = f x := hOld₀ x hx
  have hFixY : g₀ y = f y := hOld₀ y hy
  refine ⟨k, p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    obtain ⟨hxs, hsy⟩ := hBetween s.val s.property
    have hLeft : g₀ x < g₀ s.val :=
      Q₀Now.1.ordered x s.val (hOldAt hx) (hAt s) hxs
    have hRight : g₀ s.val < g₀ y :=
      Q₀Now.1.ordered s.val y (hAt s) (hOldAt hy) hsy
    rw [hFixX, hValue₀ s] at hLeft
    rw [hValue₀ s, hFixY] at hRight
    exact ⟨hLeft, hRight⟩
  · intro s t hst
    have hOrder : g₀ s.val < g₀ t.val :=
      Q₀Now.1.ordered s.val t.val (hAt s) (hAt t) hst
    rwa [hValue₀ s, hValue₀ t] at hOrder
  · intro s hLeaf
    have hRole := Q₀Now.1.leaf_role s.val (hAt s) hLeaf
    rwa [hValue₀ s] at hRole
  · intro s hOne
    have hRole := Q₀Now.1.one_split_role s.val (hAt s) hOne
    rwa [hValue₀ s] at hRole
  · intro s hTwo
    have hRole := Q₀Now.1.two_split_role s.val (hAt s) hTwo
    rwa [hValue₀ s] at hRole
  · intro s hLeaf
    obtain ⟨i, hi⟩ := Q₀Now.1.leaf_range s.val (hAt s) hLeaf
    exact ⟨i, (hValue₀ s).symm.trans hi⟩
  · intro a b c hab hbc
    have hEdge := Q₀Now.1.induced_edge
      a.val b.val c.val (hAt a) (hAt b) (hAt c) hab hbc
    rwa [hValue₀ a, hValue₀ b, hValue₀ c] at hEdge
  · intro n
    exact hAll n

end DiaryLeafPriority
end ThreeUniformDiaries
