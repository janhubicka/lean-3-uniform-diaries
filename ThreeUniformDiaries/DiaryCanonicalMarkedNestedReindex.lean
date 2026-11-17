import ThreeUniformDiaries.DiaryCanonicalMarkedNestedSupport
import ThreeUniformDiaries.DiaryFiniteLowerCanonicalSupport

/-!
# Canonical finite reindexing composes across nested supports

Take arbitrary finite T ⊆ S of natural-number vertices.
The canonical increasing rank r_S is strictly increasing on S.
Its restriction to T is an injection, so T and its rank image
have equal cardinality. The sorted enumeration of that image
is literally the rank of the sorted enumeration of T.

This is a finite-set theorem independent of diary axioms;
it supplies the missing reindexing stage in the appendix's
nested marked-diary support lemma.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Rank is injective on every finite subset T of its support S. -/
theorem finiteSupportRank_injOn_subset
    (S T : Finset Nat) (hTS : T ⊆ S) :
    Set.InjOn (finiteSupportRank S) (T : Set Nat) := by
  intro a ha b hb heq
  have haS : a ∈ S := hTS ha
  have hbS : b ∈ S := hTS hb
  have hra := (finiteSupportRank_spec S a haS).2
  have hrb := (finiteSupportRank_spec S b hbS).2
  calc
    a = finiteSupportIndex S (finiteSupportRank S a) := hra.symm
    _ = finiteSupportIndex S (finiteSupportRank S b) :=
      congrArg (finiteSupportIndex S) heq
    _ = b := hrb

/-- The canonical ranks of nested supports preserve their sizes. -/
theorem finiteSupportRank_image_card
    (S T : Finset Nat) (hTS : T ⊆ S) :
    (T.image (finiteSupportRank S)).card = T.card := by
  classical
  exact Finset.card_image_of_injOn
    (finiteSupportRank_injOn_subset S T hTS)

/-- If T ⊆ S, sorting T and then taking ranks in S is identical
to sorting the rank-image T inside S. This is a LITERAL equality
of values at every genuine finite index, not just existence of
some order isomorphism. -/
theorem finiteSupportIndex_nested_rank_image
    (S T : Finset Nat) (hTS : T ⊆ S)
    (i : Nat) (hi : i < T.card) :
    finiteSupportIndex (T.image (finiteSupportRank S)) i =
      finiteSupportRank S (finiteSupportIndex T i) := by
  classical
  let V : Finset Nat := T.image (finiteSupportRank S)
  have hCard : V.card = T.card :=
    finiteSupportRank_image_card S T hTS
  have hMem (j : Fin T.card) :
      finiteSupportRank S (finiteSupportIndex T j.val) ∈ V := by
    exact Finset.mem_image.mpr
      ⟨finiteSupportIndex T j.val,
        finiteSupportIndex_mem T j.val j.isLt,rfl⟩
  have hMono :
      StrictMono (fun j : Fin T.card =>
        finiteSupportRank S (finiteSupportIndex T j.val)) := by
    intro j k hjk
    have hOrig :
        finiteSupportIndex T j.val < finiteSupportIndex T k.val :=
      finiteSupportIndex_strictMono T j.val k.val hjk k.isLt
    exact finiteSupportRank_lt S
      (hTS (finiteSupportIndex_mem T j.val j.isLt))
      (hTS (finiteSupportIndex_mem T k.val k.isLt)) hOrig
  have hUnique :
      (fun j : Fin T.card =>
        finiteSupportRank S (finiteSupportIndex T j.val)) =
      V.orderEmbOfFin hCard :=
    Finset.orderEmbOfFin_unique hCard hMem hMono
  have hiV : i < V.card := by rw [hCard]; exact hi
  calc
    finiteSupportIndex V i = V.orderEmbOfFin rfl ⟨i,hiV⟩ :=
      finiteSupportIndex_of_lt V i hiV
    _ = V.orderEmbOfFin hCard ⟨i,hi⟩ := by
      apply (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff).2
      rfl
    _ = finiteSupportRank S (finiteSupportIndex T i) := by
      simpa only using (congrFun hUnique ⟨i,hi⟩).symm

end DiaryLeafPriority
end ThreeUniformDiaries
