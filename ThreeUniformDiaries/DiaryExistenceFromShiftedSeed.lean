import ThreeUniformDiaries.DiaryShiftedSeedPrediary
import ThreeUniformDiaries.DiaryOnePassCompleteS2
import ThreeUniformDiaries.DiaryOnePassTargetLeafCones

/-!
# Track B: exact countable diary existence from one remaining seed V3 lemma

The manuscript's thm:amend says EVERY enumerated countable 3-graph H
is order-isomorphic to the complete leaf reduct of a full countable
diary D. The printed construction invokes a pre-diary completion
lemma whose universal old-cut preservation is false.

We instead use the already verified static one-pass diary completion:
1. put three markers before H, with its true Devlin comparison bits;
2. verify this shifted seed is a genuine V/E pre-diary;
3. apply onePassRawTarget_isDiary;
4. use the verified exact target leaf census and literal induced
   old-vertex embedding, with no spurious new leaves.

All of steps 2--4 are established here conditional ONLY on the
source-to-shifted-seed LexEarlier equivalence. That final seed V3
gate is explicit, not silently inferred from the marker assignment.
The claim is therefore conditional and does not validate thm:amend.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every increasing old triple is embedded by a +3 shift.
This preserves AND reflects edges and nonedges. -/
noncomputable def shiftedDiarySeed_embedding (H : Ordered3Graph Nat) :
    Ordered3Graph.Embedding H (shiftedDiarySeed H) where
  toFun := fun u => u + 3
  strictMono := by
    intro i j hij
    omega
  edge_iff := by
    intro a b c hab hbc
    exact (shiftedDiarySeed_leaf_edge_iff H a b c hab hbc).symm

/-- The shifted source is order-isomorphic to the COMPLETE leaf
reduct of a full countable diary, assuming just the actual
lexicographic V3 transport through the three-marker seed.

No source 1-/2-type old-cut preservation is assumed, and no
diary Ramsey theorem or countable unavoidability is used. -/
theorem exists_countable_full_diary_with_exact_leaf_reduct_of_seed_lex
    (H : Ordered3Graph Nat)
    (hLex : ∀ a b : Nat, a < b →
      (LexEarlier (shiftedDiarySeed H) (a+3) (b+3) ↔
        LexEarlier H a b)) :
    ∃ (D : Ordered3Graph Nat),
      RoleDiary D ∧
        ∃ e : Ordered3Graph.Embedding H D,
          (∀ u : Nat, IsLeaf D (e u)) ∧
          (∀ v : Nat, IsLeaf D v → ∃ u : Nat, e u = v) := by
  let S := shiftedDiarySeed H
  let D := onePassRawTarget S
  have hPrediary : RolePrediary S :=
    shiftedDiarySeed_isPrediary_of_lex H hLex
  let e : Ordered3Graph.Embedding H D :=
    (onePassRawEmbedding S).comp (shiftedDiarySeed_embedding H)
  refine ⟨D, onePassRawTarget_isDiary hPrediary, e, ?_, ?_⟩
  · intro u
    have hLeaf : IsLeaf S (u+3) :=
      shiftedDiarySeed_old_isLeaf H (u+3) (by omega)
    exact (onePassRawTarget_leaf_iff_oldLeaf_image S (e u)).mpr
      ⟨u+3,hLeaf,rfl⟩
  · intro v hv
    obtain ⟨x,hx,hxv⟩ :=
      (onePassRawTarget_leaf_iff_oldLeaf_image S v).mp hv
    have hx3 : 3 ≤ x := hx.1
    refine ⟨x-3, ?_⟩
    change onePassOldImage S ((x-3)+3) = v
    rw [Nat.sub_add_cancel hx3]
    exact hxv

end DiaryLeafPriority
end ThreeUniformDiaries
