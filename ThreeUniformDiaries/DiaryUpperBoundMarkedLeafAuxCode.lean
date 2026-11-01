import ThreeUniformDiaries.DiaryUpperBoundFiniteSupportActualCode

/-!
# Track A: every finite diary leaf tuple has an actual marked ATR code

The conditional upper-bound palette from Track A PRs #976/#981
requires a marked finite source representation for each labelled
finite copy of A. The *geometric* half is now direct:

Given a full countable RoleDiary D and any FINITE labelled list
of genuine leaves, take the literal finite set L of those leaves,
construct its canonical finite full leaf-meet support, and use
the unconditional finite auxiliary embedding from PR #999.

Every prescribed leaf has a unique selected finite support index.
The actual finite ATR code sends that index to exactly the
prescribed original leaf. The marked source vertices remain genuine
leaves after finite compression. No unproved classifying theorem,
countable unavoidability, or final Ramsey theorem is invoked.

Remaining sharp upper-bound work: enumerate the genuinely possible
marked finite full diary types independently of the ambient D,
show their number is the claimed diary count (including labels),
and compose with the global canonical aux embedding of D into G.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

variable {G : Ordered3Graph Nat}

/-- An arbitrary labelled finite tuple of genuine diary leaves
has an ACTUAL finite auxiliary embedding code of its complete
generated finite diary, with a marking of exactly the prescribed
leaves. Source copies may have repeated labelled coordinates:
the theorem does not silently impose injectivity, ordering or
an A-edge table. Those are later imposed by the labelled-A
classification lemma and its automorphism factor. -/
theorem finiteLeafTuple_has_marked_actualAuxCode
    (D : RoleDiary G) (a : Nat)
    (v : Fin a → Nat)
    (hLeaf : ∀ i : Fin a, IsLeaf G (v i)) :
    ∃ L : Finset Nat,
      L = (Finset.univ : Finset (Fin a)).image v ∧
      (∀ u : Nat, u ∈ L → IsLeaf G u) ∧
      ∃ e : ThreeUniformDiaries.Ordered3Graph.FiniteAuxEmbeddingImage
          ((finiteSupportGraph G (finiteLeafMeetSupport G L)).initialSegment
            (finiteLeafMeetSupport G L).card).toOrdered3Graph
          G (finiteLeafMeetSupport G L).card,
        ∃ marked : Fin a → Fin (finiteLeafMeetSupport G L).card,
          (∀ i : Fin a, v i = e.image (marked i)) ∧
          (∀ i : Fin a,
            IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L))
              (marked i).val) := by
  classical
  let L : Finset Nat := (Finset.univ : Finset (Fin a)).image v
  let S : Finset Nat := finiteLeafMeetSupport G L
  let H : Ordered3Graph Nat := finiteSupportGraph G S
  have hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u := by
    intro u hu
    obtain ⟨i,_,heq⟩ := Finset.mem_image.mp hu
    subst u
    exact hLeaf i
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker G L 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker G L 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker G L 2 (by omega)
  have hSupport (i : Fin a) : v i ∈ S := by
    apply mem_finiteLeafMeetSupport_leaf
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  let chosen (i : Fin a) : Nat :=
    Classical.choose (finiteSupportIndex_surjective_on S (v i) (hSupport i))
  have chosen_spec (i : Fin a) :
      chosen i < S.card ∧ finiteSupportIndex S (chosen i) = v i :=
    Classical.choose_spec
      (finiteSupportIndex_surjective_on S (v i) (hSupport i))
  let marked (i : Fin a) : Fin S.card :=
    ⟨chosen i, (chosen_spec i).1⟩
  let e : ThreeUniformDiaries.Ordered3Graph.FiniteAuxEmbeddingImage
      (H.initialSegment S.card).toOrdered3Graph G S.card :=
    finiteLeafMeetSupport_actualAuxCode D hLeaves
  refine ⟨L, rfl, hLeaves, e, marked, ?_, ?_⟩
  · intro i
    have hCode : e.image (marked i) =
        finiteSupportIndexTotal S (chosen i) := by
      rfl
    calc
      v i = finiteSupportIndex S (chosen i) :=
        (chosen_spec i).2.symm
      _ = finiteSupportIndexTotal S (chosen i) :=
        (finiteSupportIndexTotal_inside S (chosen i)
          (chosen_spec i).1).symm
      _ = e.image (marked i) := hCode.symm
  · intro i
    have hOldLeaf : IsLeaf G (finiteSupportIndex S (chosen i)) := by
      rw [(chosen_spec i).2]
      exact hLeaf i
    have hi3 : 3 ≤ chosen i :=
      finiteSupportIndex_ge_three_of_image S
        (chosen i) h0 h1 h2 (chosen_spec i).1 hOldLeaf.1
    exact
      (finiteSupportGraph_leaf_iff
        (G := G) (S := S) h0 h1 h2
        (chosen i) hi3 (chosen_spec i).1).mpr hOldLeaf

end DiaryLeafPriority
end ThreeUniformDiaries
