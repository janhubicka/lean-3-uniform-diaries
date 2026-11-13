import ThreeUniformDiaries.DiaryFiniteCandidatePersistentFusion
import ThreeUniformDiaries.DiaryPersistentSuccessorBoundEquivalence
import ThreeUniformDiaries.DiaryPersistentOrOmittedVirtualType

/-!
# Track D: a failed strong countable diary embedding forces a persistent escape witness

This is an adversarial, explicitly CONTRAPOSITIVE reduction, not
the missing geometric proof of countable unavoidability.

If a full countable embedding into the original prescribed universal
leaf range, preserving both exact numerical leaf meets, does not exist,
then some finitely persistent genuine old reserved stage has NO
compatible persistent next-leaf successor. The marker base, nonleaf
steps and conditional finite-cover fusion theorem are ALREADY
checked: if no such failing persistent leaf step existed, every
persistent source leaf stage would have a finite next-image cover,
and the checked fusion theorem would construct the embedding.

At that failing old stage, the verified joint full split-profile /
complete mixed-colour dichotomy supplies a fixed finite profile p
and old-cut colour c0, valid at EVERY finite future source horizon,
and a cofinally recurrent coherent ALL-CUT mixed singleton limit type
cInf which is omitted by every actual target leaf. The finite
approximants all agree with the same old support and nonleaf record.

This identifies a necessary local certificate for failure of the
strong full-embedding conclusion. Such omitted types are possible in
genuine countable RoleDiaries; nothing here proves the strong
embedding theorem, countable unavoidability, or BRDs. It also does
not assert that absence of a strong full-meet embedding is equivalent
to failure of a weaker preembedding formulation.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- If the STRONG exact-meet countable embedding conclusion in the
original prescribed leaf range is false, an ACTUAL finitely
persistent old reserved stage must fail to have a compatible
finitely persistent next-leaf successor.

This is the constructive-content (in classical logic) contraposition
of already certified finite-cover fusion. It is NOT a new existence
theorem for the missing finite next-image covers. -/
theorem exists_persistent_leaf_without_persistent_successor_of_no_full_embedding
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (hUniversal : Ordered3Graph.CountablyUniversal U)
    (F : Ordered3Graph.UnorderedEmbedding U K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (hNo : ¬ ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d))) :
    ∃ m : Nat, ∃ f : Nat → Nat,
      IsLeaf H m ∧
      PersistentReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ¬ (∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K
          (fun t : Nat => F t) (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g) := by
  classical
  have hBad :
      ∃ m : Nat, ∃ f : Nat → Nat,
        IsLeaf H m ∧
        PersistentReservedDiaryStage H K (fun t : Nat => F t) m f ∧
        ¬ FiniteHorizonNextLeafCover
          H K (fun t : Nat => F t) m f := by
    by_contra hNone
    apply hNo
    apply exists_fullDiaryEmbedding_of_persistent_finite_covers
      DH DK G hUniversal F hFLeaf
    intro m hm f P
    by_contra hNoCover
    apply hNone
    exact ⟨m, f, hm, P, hNoCover⟩
  obtain ⟨m, f, hm, P, hNoCover⟩ := hBad
  refine ⟨m, f, hm, P, ?_⟩
  intro hSucc
  exact hNoCover
    ((persistentSuccessor_iff_finiteHorizonNextLeafCover hm).mp hSucc)

/-- Strong nonunavoidability forces a very specific ACTUAL
finite-stage witness: a persistent old reserved support f, one fixed
new nonleaf generator record p and one complete old-cut colour c0,
realized with that same f,p,c0 at every finite future horizon,
together with a coherent full mixed singleton type cInf whose
finite prefixes recur at arbitrarily late horizons but which NO
genuine target leaf realizes.

This theorem is necessary, not sufficient, for failure of the
strong countable embedding. Omission itself is not a contradiction:
full countable diaries need not be countably saturated. -/
theorem exists_omitted_joint_mixed_type_of_no_full_embedding
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (hUniversal : Ordered3Graph.CountablyUniversal U)
    (F : Ordered3Graph.UnorderedEmbedding U K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (hNo : ¬ ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d))) :
    ∃ m : Nat, ∃ f : Nat → Nat,
      IsLeaf H m ∧
      PersistentReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat),
        ∃ c0 : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
          (∀ n : Nat,
            HasJointProfileColourHorizon H K
              (fun t : Nat => F t) f m p c0 n) ∧
          ∃ cInf : (B : Nat) → Fin B → Fin B → Bool,
            (∀ (B : Nat) (x y : Fin B),
              cInf (B + 1) x.castSucc y.castSucc = cInf B x y) ∧
            cInf (oldStageTailCut H m f) = c0 ∧
            (∀ B N : Nat, ∃ n : Nat, N ≤ n ∧
              ∃ g : Nat → Nat,
                ReservedDiaryStage H K
                  (fun t : Nat => F t) (m + 1 + n) g ∧
                CofinalDiaryStageCompatible H m f g ∧
                (∀ u : {u : Nat //
                  u ∈ newNonleafGeneratorSupport H m},
                  g u.val = p u) ∧
                DiaryLowerBoundColors.singletonColour K
                  (oldStageTailCut H m f) (g m) = c0 ∧
                DiaryLowerBoundColors.singletonColour K B (g m) =
                  cInf B) ∧
            ¬ ∃ v : Nat, IsLeaf K v ∧
              ∀ B : Nat,
                DiaryLowerBoundColors.singletonColour K B v =
                  cInf B := by
  classical
  obtain ⟨m, f, hm, P, hNoSucc⟩ :=
    exists_persistent_leaf_without_persistent_successor_of_no_full_embedding
      DH DK G hUniversal F hFLeaf hNo
  obtain ⟨p, c0, hAll, hDich⟩ :=
    DK.persistent_stage_persistent_or_omitted_virtual_mixed_type hm P
  rcases hDich with hSucc | ⟨cInf, hProj, hOldColour, hRecur, hOmitted⟩
  · obtain ⟨g, Pg, hKeep, _hProfile, _hColour⟩ := hSucc
    exact False.elim (hNoSucc ⟨g, Pg, hKeep⟩)
  · exact ⟨m, f, hm, P, p, c0, hAll,
      cInf, hProj, hOldColour, hRecur, hOmitted⟩

end DiaryLeafPriority
end ThreeUniformDiaries
