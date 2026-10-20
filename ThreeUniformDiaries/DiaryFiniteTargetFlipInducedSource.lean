import ThreeUniformDiaries.DiaryFiniteFlipInducedPullback
import ThreeUniformDiaries.DiaryFiniteLeafPreembeddingComposition
import ThreeUniformDiaries.DiaryFiniteFamilyCountableCompletion
import ThreeUniformDiaries.DiaryFiniteFlipTargetTransport

/-!
# Any target diary flip induces an actual source diary flip

Suppose A is a genuine bounded finite diary, A -> B is a
protected finite meet embedding, and B' is a flip of B.

The original source map is still a finite LEAF preembedding
A -> B' (verified target-flip transport), but need no longer
preserve split-containing mixed numerical meets.

Embed B' faithfully in a countable RoleDiary G by the verified
single-input countable completion. Composing the leaf
preembedding with the protected B' -> G embedding gives a
leaf preembedding A -> G. The exact leaf-image closure and
induced-reduct theorems then produce an actual finite diary
A' on precisely the source n vertices, such that A' is a
FLIP of A and its edge/nonedge relation is literally the
pullback of B' along the original source map.

No claim is made that the map A' -> B' preserves mixed
numerical meets. The theorem does NOT give an embedding of
the UNFLIPPED source A into every target flip: that requires
a family of suitably causal embeddings and additional
mixed-meet protection when needed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A B B' : Ordered3Graph Nat}
variable {n k : Nat} {f : Nat → Nat}

/-- Every finite diary has a faithful protected copy in a genuine
countable RoleDiary, by the previously verified finite-family
completion with a singleton input list. -/
theorem exists_countableDiary_for_finiteDiary
    (DB : FiniteRoleDiaryBlock B' k) :
    ∃ (G : Ordered3Graph Nat), RoleDiary G ∧
      ∃ (h : Nat → Nat), FiniteMeetEmbedding B' G k h := by
  let D : FiniteDiaryInput := ⟨B',k,DB⟩
  obtain ⟨G,DG,hCopies⟩ :=
    exists_countableDiary_for_finiteFamily [D]
  obtain ⟨h,Eh⟩ := hCopies D (by simp)
  exact ⟨G,DG,h,Eh⟩

/-- The literal induced finite RELATIONAL pullback of B' along
f is always a genuine finite flip of A.

This is the correct geometric pullback existence theorem.
Its conclusion includes all leaf singleton/full pair meets
but deliberately makes no claim about mixed target meets. -/
theorem exists_inducedSourceFlip_of_targetFlip
    (DA : FiniteRoleDiaryBlock A n)
    (E : FiniteMeetEmbedding A B n f)
    (hRange : ∀ u : Nat, u < n → f u < k)
    (F : FiniteDiaryFlip B B' k) :
    ∃ A' : Ordered3Graph Nat,
      FiniteDiaryFlip A A' n ∧
      (∀ a b c : Nat, a < b → b < c → c < n →
        (A'.edge a b c ↔ B'.edge (f a) (f b) (f c))) := by
  obtain ⟨G,DG,h,Eh⟩ :=
    exists_countableDiary_for_finiteDiary F.target_diary
  let Q : FiniteLeafPreembedding A B' n k f :=
    E.leafPreembedding_after_target_flip hRange F
  let R : FiniteLeafPreembedding A G n (h k)
      (fun u => h (f u)) :=
    Q.comp_meetEmbedding Eh
  let S := finiteLeafMeetSupport G
    (finiteDiaryLeafImage A n (fun u => h (f u)))
  let A' := finiteSupportGraph G S
  refine ⟨A',finiteLeafPreembedding_support_is_flip DA DG R,?_⟩
  intro a b c hab hbc hcn
  have hOld := finiteLeafPreembedding_support_edge_iff
    DA R a b c hab hbc hcn
  have hNew : G.edge (h (f a)) (h (f b)) (h (f c)) ↔
      B'.edge (f a) (f b) (f c) :=
    Eh.edge_iff (f a) (f b) (f c)
      (E.strictMono hab) (E.strictMono hbc)
      (hRange c hcn)
  exact hOld.trans hNew

end DiaryLeafPriority
end ThreeUniformDiaries
