import ThreeUniformDiaries.DiaryCountableRelativeStepExtension

/-!
# Certified (pruned) countable diary fusion

The hypothesis that EVERY admissible finite support embedding extends
may be much stronger than the actual countable unavoidability argument
requires: there can be admissible dead-end maps.

Here a user-supplied predicate Safe m f certifies a selectable finite
support map. We require only an initial SAFE map and an extension for
each SAFE map, preserving all images on its old support. Other
admissible maps need not extend.

This is genuine infinite fusion, yielding the same full induced
countable embedding as the previous gluing theorem. Nothing here
proves that the requisite Safe predicate exists from finite flip
absorption; that is the remaining mathematical obligation.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A selected subsystem of finite stage maps and its verified
one-step extension rule. The Safe predicate may encode future
capacity, a reservoir, rank constraints, or other invariants. -/
structure CertifiedDiaryFusionData
    {H : Ordered3Graph Nat} (DH : RoleDiary H)
    (K : Ordered3Graph Nat) (F : Nat → Nat) where
  Safe : Nat → (Nat → Nat) → Prop
  valid : ∀ m f, Safe m f → AdmissibleCofinalDiaryStage H K F m f
  initial : ∃ f : Nat → Nat, Safe 0 f
  next : ∀ m f, Safe m f →
    ∃ g : Nat → Nat, Safe (m + 1) g ∧
      ∀ u : Nat, u ∈ countableDiaryFiniteSupport H m → g u = f u

namespace CertifiedDiaryFusionData

variable {H K : Ordered3Graph Nat} {DH : RoleDiary H}
variable {F : Nat → Nat}

/-- Every certified fusion system yields a single coherent
countable family of actual admissible finite support maps. -/
theorem exists_coherent
    (C : CertifiedDiaryFusionData DH K F) :
    ∃ P : CoherentCofinalDiarySupportMaps DH K,
      ∀ m u : Nat,
        u ∈ countableDiaryFiniteSupport H m →
        IsLeaf H u → ∃ t : Nat, P.map m u = F t := by
  classical
  let start : {f : Nat → Nat // C.Safe 0 f} :=
    ⟨Classical.choose C.initial, Classical.choose_spec C.initial⟩
  let step : ∀ m : Nat,
      (p : {f : Nat → Nat // C.Safe m f}) →
      {g : Nat → Nat //
        C.Safe (m + 1) g ∧
        (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
          g u = p.1 u)} := by
    intro m p
    let h := C.next m p.1 p.2
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  let stages : ∀ m : Nat, {f : Nat → Nat // C.Safe m f} :=
    Nat.rec start (fun m p => ⟨(step m p).1, (step m p).2.1⟩)
  have hAdjacent (m u : Nat)
      (hu : u ∈ countableDiaryFiniteSupport H m) :
      (stages (m + 1)).1 u = (stages m).1 u := by
    change (step m (stages m)).1 u = (stages m).1 u
    exact (step m (stages m)).2.2 u hu
  have hCoherent (m n : Nat) (hmn : m ≤ n)
      (u : Nat) (hu : u ∈ countableDiaryFiniteSupport H m) :
      (stages m).1 u = (stages n).1 u := by
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      have huN : u ∈ countableDiaryFiniteSupport H n :=
        (countableDiaryFiniteSupport_mono H m n hmn) hu
      exact ih.trans (hAdjacent n u huN).symm
  have stageValid (m : Nat) :
      AdmissibleCofinalDiaryStage H K F m (stages m).1 :=
    C.valid m (stages m).1 (stages m).2
  let P : CoherentCofinalDiarySupportMaps DH K := {
    map := fun m => (stages m).1
    coherent := by
      intro m n hmn u hu
      exact hCoherent m n hmn u hu
    ordered := by
      intro m u v hu hv huv
      exact (stageValid m).ordered u v hu hv huv
    marker_zero := by
      intro m
      exact (stageValid m).marker_zero
    marker_one := by
      intro m
      exact (stageValid m).marker_one
    marker_two := by
      intro m
      exact (stageValid m).marker_two
    leaf_role := by
      intro m u hu hLeaf
      exact (stageValid m).leaf_role u hu hLeaf
    one_split_role := by
      intro m u hu hOne
      exact (stageValid m).one_split_role u hu hOne
    two_split_role := by
      intro m u hu hTwo
      exact (stageValid m).two_split_role u hu hTwo
    induced_edge := by
      intro m a b c ha hb hc hab hbc
      exact (stageValid m).induced_edge a b c ha hb hc hab hbc
    leaf_oneMeet := by
      intro m a b ha hb hLa hLb
      exact (stageValid m).leaf_oneMeet a b ha hb hLa hLb
    leaf_twoMeet := by
      intro m a b c d ha hb hc hd hab hcd hLa hLb hLc hLd
      exact (stageValid m).leaf_twoMeet a b c d
        ha hb hc hd hab hcd hLa hLb hLc hLd
  }
  refine ⟨P,?_⟩
  intro m u hu hLeaf
  exact (stageValid m).leaf_range u hu hLeaf

/-- A pruned fusion system, retaining only its certified
extendible stages, suffices for the full countable diary
embedding and all numerical meets. The existence of
the certificate is NOT proved by this theorem. -/
theorem exists_full_embedding
    (C : CertifiedDiaryFusionData DH K F)
    (DK : RoleDiary K) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  obtain ⟨P,hRange⟩ := C.exists_coherent
  exact P.exists_full_embedding_in_range DK F hRange

end CertifiedDiaryFusionData
end DiaryLeafPriority
end ThreeUniformDiaries
