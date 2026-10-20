import ThreeUniformDiaries.DiaryFiniteProtectedFactorization
import ThreeUniformDiaries.DiaryFiniteFamilyCountableCompletion

/-!
# One actual finite diary jointly contains any finite family

The earlier verified amalgamation theorem supplies ONE countable
completed RoleDiary G carrying exact induced numerical-meet
embeddings of any finite family of finite diaries.

Select the union of the images of the LEAVES of these finitely
many embedded finite sources. This union is finite and consists
entirely of genuine G leaves. The already verified leaf-meet
support construction extracts a genuine bounded finite diary
from that union, and protected-copy factorisation shows each
supplied source embedding survives the compression, with every
mixed singleton/full ordered-pair numerical meet preserved.

No arbitrary globally precompact flip expansion is asserted here.
In particular this proves finite-family joint embedding in the
base finite diary class; the stronger every-flip absorption
direction of the lower-bound lemma remains a separate obligation.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat}

/-- From any finite family of finite meet embeddings into G,
select a finite set containing EVERY leaf image, consisting
entirely of genuine target leaves, while retaining a valid
embedding witness for each listed source. -/
theorem exists_finiteFamily_leaf_support
    (Ds : List FiniteDiaryInput) :
    (∀ D : FiniteDiaryInput, D ∈ Ds →
      ∃ f : Nat → Nat,
        FiniteMeetEmbedding D.graph G D.bound f) →
    ∃ L : Finset Nat,
      (∀ x : Nat, x ∈ L → IsLeaf G x) ∧
      (∀ D : FiniteDiaryInput, D ∈ Ds →
        ∃ f : Nat → Nat,
          FiniteMeetEmbedding D.graph G D.bound f ∧
          (∀ u : Nat, 3 ≤ u → u < D.bound →
            IsLeaf D.graph u → f u ∈ L)) := by
  classical
  induction Ds with
  | nil =>
      intro _hMaps
      refine ⟨∅, ?_, ?_⟩
      · intro x hx
        simp at hx
      · intro D hD
        cases hD
  | cons D rest ih =>
      intro hMaps
      have hRestMaps :
          ∀ R : FiniteDiaryInput, R ∈ rest →
            ∃ f : Nat → Nat,
              FiniteMeetEmbedding R.graph G R.bound f := by
        intro R hR
        exact hMaps R (by simp [hR])
      obtain ⟨LRest,hRestLeaves,hRestWitnesses⟩ := ih hRestMaps
      obtain ⟨fD,ED⟩ := hMaps D (by simp)
      let F : Finset Nat :=
        ((Finset.Ico 3 D.bound).filter
          (fun u => IsLeaf D.graph u)).image fD
      have hFLeaves : ∀ x : Nat, x ∈ F → IsLeaf G x := by
        intro x hx
        change x ∈ ((Finset.Ico 3 D.bound).filter
          (fun u => IsLeaf D.graph u)).image fD at hx
        obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨huInterval,huLeaf⟩ := Finset.mem_filter.mp hu
        have huBounds := Finset.mem_Ico.mp huInterval
        exact (ED.leaf_iff u huBounds.1 huBounds.2).mpr huLeaf
      refine ⟨F ∪ LRest, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with hF | hRest
        · exact hFLeaves x hF
        · exact hRestLeaves x hRest
      · intro R hR
        rcases List.mem_cons.mp hR with heq | hRest
        · subst R
          refine ⟨fD, ED, ?_⟩
          intro u hu3 hu hLeaf
          apply Finset.mem_union.mpr
          left
          change fD u ∈ ((Finset.Ico 3 D.bound).filter
            (fun x => IsLeaf D.graph x)).image fD
          apply Finset.mem_image.mpr
          exact ⟨u, Finset.mem_filter.mpr
            ⟨Finset.mem_Ico.mpr ⟨hu3,hu⟩,hLeaf⟩,rfl⟩
        · obtain ⟨fR,ER,hImageRest⟩ :=
            hRestWitnesses R hRest
          refine ⟨fR,ER,?_⟩
          intro u hu3 hu hLeaf
          exact Finset.mem_union.mpr
            (Or.inr (hImageRest u hu3 hu hLeaf))

/-- Genuine finite-family joint embedding for bounded finite
diaries. The ONE common target is itself a complete bounded
finite diary; all source maps preserve induced edges, roles,
and every numerical singleton and ordered-pair meet. -/
theorem exists_finiteDiary_for_finiteFamily
    (Ds : List FiniteDiaryInput) :
    ∃ (T : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock T k ∧
      ∀ D : FiniteDiaryInput, D ∈ Ds →
        ∃ f : Nat → Nat,
          FiniteMeetEmbedding D.graph T D.bound f := by
  classical
  obtain ⟨G,DG,hCopies⟩ :=
    exists_countableDiary_for_finiteFamily Ds
  obtain ⟨L,hLeaves,hWitnesses⟩ :=
    exists_finiteFamily_leaf_support (G := G) Ds hCopies
  let S := finiteLeafMeetSupport G L
  let T := finiteSupportGraph G S
  refine ⟨T,S.card,finiteLeafMeetSupport_is_finiteDiary DG hLeaves,?_⟩
  intro D hD
  obtain ⟨f,E,hImageLeaves⟩ := hWitnesses D hD
  refine ⟨finiteSupportLift S D.bound f,?_⟩
  exact (FiniteMeetEmbedding.factor_through_leafMeetSupport
    D.diary DG E L hLeaves hImageLeaves).2

end DiaryLeafPriority
end ThreeUniformDiaries
