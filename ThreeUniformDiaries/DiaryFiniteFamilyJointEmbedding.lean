import ThreeUniformDiaries.DiaryFiniteMeetEmbeddingComposition
import ThreeUniformDiaries.DiaryFiniteSumMeetEmbeddings

/-!
# Finite families of diaries have a common protected V/E pre-diary

We iterate the actual two-block ordered-sum theorem over a list
of bounded finite diary inputs. The left accumulator requires
only V/E, while each newly added right block is a finite diary.
All previously embedded copies remain induced and preserve ALL
numerical singleton/full pair meets by composition of the
strengthened finite meet-embedding interfaces.

The empty case is a genuine finite V/E pre-diary consisting of
the three distinguished markers and no ternary edges. This avoids
assuming that a finite edge table on Nat is a global RoleDiary.

The final result is a single finite V/E pre-diary with induced,
meet-preserving embeddings for EVERY listed finite diary, and
all their nonmarker images satisfy the exact protected S1/S2
conditions. It does not assert the combined structure has S1/S2
or prove any every-flip absorption statement.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A genuinely bounded finite diary as a reusable input datum
for a heterogeneous finite family. -/
structure FiniteDiaryInput where
  graph : Ordered3Graph Nat
  bound : Nat
  diary : FiniteRoleDiaryBlock graph bound

/-- The empty ternary edge table used as the initial V/E
accumulator before adding any finite diary input. -/
def finiteEmptyThree : Ordered3Graph Nat where
  edge := fun _ _ _ => False

/-- The empty three-marker frame satisfies precisely the bounded
finite pre-diary axioms. It does NOT satisfy RolePrediary on Nat. -/
theorem finiteEmptyThree_prediary :
    FiniteRolePrediaryBlock finiteEmptyThree 3 := by
  refine {
    frame := ?_
    role_valid := ?_
    one_split_coherent := ?_
    one_split_witness := ?_
    two_split_coherent := ?_
    two_split_witness := ?_
    leaf_marker_one := ?_
    leaf_marker_two := ?_
    permitted_edge := ?_
  }
  · refine ⟨by omega, ?_⟩
    intro a b c he
    exact False.elim he
  · intro z hz3 hzBound
    omega
  · intro s a b hs _ha _hb _hA _hB
    exact False.elim hs.2.1
  · intro s hs hsBound
    have hs3 := hs.1
    omega
  · intro s a b c d hs _hab _hcd _ha _hb _hc _hd _hAB _hCD
    exact False.elim hs.2.2
  · intro s hs hsBound
    have hs3 := hs.1
    omega
  · intro a b hab hbn ha _hb
    exfalso
    have ha3 := ha.1
    omega
  · intro a b hab hbn ha _hb
    exfalso
    have ha3 := ha.1
    omega
  · intro x y z he
    exact False.elim he

/-- An arbitrary finite list of finite diaries admits ONE
bounded finite V/E pre-diary target in which every source
has a genuine induced finite meet embedding, with its entire
nonmarker image lying inside the target finite bound. -/
theorem exists_finiteFamily_meetEmbeddings
    (Ds : List FiniteDiaryInput) :
    ∃ (G : Ordered3Graph Nat) (k : Nat),
      FiniteRolePrediaryBlock G k ∧
      ∀ D : FiniteDiaryInput, D ∈ Ds →
        ∃ f : Nat → Nat,
          FiniteMeetEmbedding D.graph G D.bound f ∧
          (∀ u : Nat, 3 ≤ u → u < D.bound → f u < k) := by
  induction Ds with
  | nil =>
      refine ⟨finiteEmptyThree, 3, finiteEmptyThree_prediary, ?_⟩
      intro D hD
      cases hD
  | cons D rest ih =>
      obtain ⟨H,n,PH,hOld⟩ := ih
      obtain ⟨bits,PG,ELeft,ERight⟩ :=
        exists_finiteTwoBlock_both_meetEmbeddings PH D.diary
      let G := finiteTwoBlockCarrier H D.graph n D.bound bits
      let k := finiteTwoBlockLength n D.bound
      refine ⟨G,k,PG,?_⟩
      intro A hA
      rcases List.mem_cons.mp hA with hNew | hExisting
      · subst A
        refine ⟨rightBlockImage n, ERight, ?_⟩
        intro u hu3 huBound
        exact rightBlockImage_lt_finiteTwoBlockLength
          n D.bound u PH.frame.length_ge_three
          D.diary.prediary.frame.length_ge_three hu3 huBound
      · obtain ⟨f,Ef,hRange⟩ := hOld A hExisting
        have Ecomp : FiniteMeetEmbedding A.graph G A.bound
            ((fun x : Nat => x) ∘ f) :=
          Ef.comp ELeft PH.frame.length_ge_three hRange
        refine ⟨((fun x : Nat => x) ∘ f), Ecomp, ?_⟩
        intro u hu3 huBound
        have huOld : f u < n := hRange u hu3 huBound
        have hnBound : n ≤ k := by
          have hRight3 := D.diary.prediary.frame.length_ge_three
          dsimp [k, finiteTwoBlockLength]
          omega
        change f u < k
        omega

/-- Strong finite-family joint embedding: every input appears
as a genuinely induced, role- and meet-preserving copy, and
its nonmarker image is a protected S1/S2 picture in the SAME
finite V/E target, bounded inside the target frame. -/
theorem exists_finiteFamily_protectedPictures
    (Ds : List FiniteDiaryInput) :
    ∃ (G : Ordered3Graph Nat) (k : Nat),
      FiniteRolePrediaryBlock G k ∧
      ∀ D : FiniteDiaryInput, D ∈ Ds →
        ∃ f : Nat → Nat,
          FiniteMeetEmbedding D.graph G D.bound f ∧
          FiniteProtectedMeetPicture G (finiteMeetImage D.bound f) ∧
          (∀ u : Nat, u ∈ finiteMeetImage D.bound f → u < k) := by
  classical
  obtain ⟨G,k,PG,hMaps⟩ :=
    exists_finiteFamily_meetEmbeddings Ds
  refine ⟨G,k,PG,?_⟩
  intro D hD
  obtain ⟨f,E,hRange⟩ := hMaps D hD
  refine ⟨f,E,E.protected_picture D.diary,?_⟩
  intro u hu
  change u ∈ (Finset.Ico 3 D.bound).image f at hu
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
  have hvBounds := Finset.mem_Ico.mp hv
  exact hRange v hvBounds.1 hvBounds.2

end DiaryLeafPriority
end ThreeUniformDiaries
