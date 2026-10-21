import ThreeUniformDiaries.DiaryFiniteRealizedFlipFeedback
import ThreeUniformDiaries.DiaryFiniteCanonicalPullbackHitting

/-!
# Adversarial audit: raw finite flip codes contain duplicate diaries

The raw finite code is a Boolean function on ALL triples of Fin n,
but the decoder discards non-increasing triples. Toggling the
irrelevant bit at (0,0,0) changes the code without changing the
represented diary. Both codes belong to the existing raw flip orbit.

At the identity target flip B->B, any chosen protected copy map
pulls back its original source diary. Thus these distinct raw
codes produce IDENTICAL feedback values regardless of map choices.

The raw-orbit feedback cannot be injective even at the identity.
The remaining absorption problem needs canonical, normalized codes.
This does not refute the mathematical diary flip property.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Toggle the irrelevant repeated-vertex triple bit (0,0,0). -/
noncomputable def finiteDiaryToggleDiagonalCode
    {n : Nat} (c : FiniteDiaryEdgeCode n) :
    FiniteDiaryEdgeCode n :=
  fun a b d =>
    if a.val = 0 ∧ b.val = 0 ∧ d.val = 0 then
      Bool.not (c a b d)
    else c a b d

/-- The two Boolean tables decode to exactly the same graph. -/
theorem finiteDiaryCodeGraph_toggleDiagonal
    (n : Nat) (c : FiniteDiaryEdgeCode n) :
    finiteDiaryCodeGraph n (finiteDiaryToggleDiagonalCode c) =
      finiteDiaryCodeGraph n c := by
  apply finiteDiary_graph_ext
  intro a b d
  have hvalid : a < b → ¬ (a = 0 ∧ b = 0 ∧ d = 0) := by
    intro hab hh
    omega
  constructor
  · rintro ⟨ha,hb,hd,hab,hbd,hbit⟩
    refine ⟨ha,hb,hd,hab,hbd,?_⟩
    have hNot := hvalid hab
    simpa [finiteDiaryToggleDiagonalCode, hNot] using hbit
  · rintro ⟨ha,hb,hd,hab,hbd,hbit⟩
    refine ⟨ha,hb,hd,hab,hbd,?_⟩
    have hNot := hvalid hab
    simpa [finiteDiaryToggleDiagonalCode, hNot] using hbit

/-- If vertex zero exists, toggling that bit changes the raw code. -/
theorem finiteDiaryToggleDiagonalCode_ne
    (n : Nat) (hn : 0 < n) (c : FiniteDiaryEdgeCode n) :
    finiteDiaryToggleDiagonalCode c ≠ c := by
  intro hEq
  let z : Fin n := ⟨0,hn⟩
  have hPoint := congrArg
    (fun t : FiniteDiaryEdgeCode n => t z z z) hEq
  have hVal : Bool.not (c z z z) = c z z z := by
    simpa [finiteDiaryToggleDiagonalCode, z] using hPoint
  cases h : c z z z <;> simp [h] at hVal

/-- The raw flip orbit is closed under changing this irrelevant bit. -/
theorem finiteSourceFlipCodes_toggleDiagonal_mem
    (A : Ordered3Graph Nat) (n : Nat)
    (c : FiniteDiaryEdgeCode n)
    (hc : c ∈ finiteSourceFlipCodes A n) :
    finiteDiaryToggleDiagonalCode c ∈ finiteSourceFlipCodes A n := by
  apply (mem_finiteSourceFlipCodes_iff A n _).mpr
  rw [finiteDiaryCodeGraph_toggleDiagonal]
  exact (mem_finiteSourceFlipCodes_iff A n c).mp hc

/-- Identity-target feedback returns the CANONICAL edge table of
the input's decoded source diary, independently of the chosen map. -/
theorem realizedSourceFlipFeedback_refl_val
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DB : FiniteRoleDiaryBlock B k)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n}) :
    (realizedSourceFlipFeedback A B B n k hCopies
      (FiniteDiaryFlip.refl DB) c).val =
      finiteDiaryEdgeCode (finiteDiaryCodeGraph n c.val) n := by
  let P := finiteDiaryCodeGraph n c.val
  let f := chosenRealizedSourceFlipMap A B n k hCopies c
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c.val).mp c.property
  have EP : FiniteBoundedMeetEmbedding P B n k f :=
    chosenRealizedSourceFlipMap_spec A B n k hCopies c
  have hPull : finiteDiaryPullbackGraph B n f = P :=
    (finiteDiaryPullbackGraph_eq_source_iff_boundedEmbedding
      FP.target_diary EP (FiniteDiaryFlip.refl DB)).mpr EP
  rw [realizedSourceFlipFeedback_val, hPull]

/-- Any two raw codes of the same decoded diary collide at the
identity target, regardless of their chosen protected embeddings. -/
theorem realizedSourceFlipFeedback_refl_eq_of_graph
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DB : FiniteRoleDiaryBlock B k)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (c d : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n})
    (hGraph : finiteDiaryCodeGraph n c.val =
      finiteDiaryCodeGraph n d.val) :
    realizedSourceFlipFeedback A B B n k hCopies
      (FiniteDiaryFlip.refl DB) c =
    realizedSourceFlipFeedback A B B n k hCopies
      (FiniteDiaryFlip.refl DB) d := by
  apply Subtype.ext
  calc
    (realizedSourceFlipFeedback A B B n k hCopies
      (FiniteDiaryFlip.refl DB) c).val =
        finiteDiaryEdgeCode (finiteDiaryCodeGraph n c.val) n :=
      realizedSourceFlipFeedback_refl_val A B n k DB hCopies c
    _ = finiteDiaryEdgeCode (finiteDiaryCodeGraph n d.val) n := by
      rw [hGraph]
    _ = (realizedSourceFlipFeedback A B B n k hCopies
        (FiniteDiaryFlip.refl DB) d).val :=
      (realizedSourceFlipFeedback_refl_val
        A B n k DB hCopies d).symm

/-- The raw-code feedback is NONINJECTIVE for B'=B, independent
of how the family of protected embeddings was selected. -/
theorem realizedSourceFlipFeedback_refl_not_injective
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (DB : FiniteRoleDiaryBlock B k)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f) :
    ¬ Function.Injective
      (realizedSourceFlipFeedback A B B n k hCopies
        (FiniteDiaryFlip.refl DB)) := by
  have hn : 0 < n := by
    have h3 := DA.prediary.frame.length_ge_three
    omega
  let c := finiteDiaryEdgeCode A n
  let d := finiteDiaryToggleDiagonalCode c
  have hc : c ∈ finiteSourceFlipCodes A n :=
    finiteSourceFlipCodes_baseline_mem DA
  have hd : d ∈ finiteSourceFlipCodes A n :=
    finiteSourceFlipCodes_toggleDiagonal_mem A n c hc
  let x : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n} := ⟨c,hc⟩
  let y : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n} := ⟨d,hd⟩
  have hDifferent : x ≠ y := by
    intro hxy
    have hCodes : c = d := congrArg Subtype.val hxy
    exact finiteDiaryToggleDiagonalCode_ne n hn c hCodes.symm
  have hSameGraph :
      finiteDiaryCodeGraph n x.val =
        finiteDiaryCodeGraph n y.val :=
    (finiteDiaryCodeGraph_toggleDiagonal n c).symm
  intro hInj
  exact hDifferent (hInj
    (realizedSourceFlipFeedback_refl_eq_of_graph
      A B n k DB hCopies x y hSameGraph))

/-- The earlier premise of injectivity under EVERY target flip
is impossible on the raw-code domain. -/
theorem realizedSourceFlipFeedback_raw_global_injectivity_impossible
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (DB : FiniteRoleDiaryBlock B k)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f) :
    ¬ (∀ B' : Ordered3Graph Nat,
      ∀ F : FiniteDiaryFlip B B' k,
        Function.Injective
          (realizedSourceFlipFeedback A B B' n k hCopies F)) := by
  intro h
  have hBad :=
    realizedSourceFlipFeedback_refl_not_injective
      A B n k DA DB hCopies
  exact hBad (h B (FiniteDiaryFlip.refl DB))

end DiaryLeafPriority
end ThreeUniformDiaries
