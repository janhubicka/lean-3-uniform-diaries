import ThreeUniformDiaries.DiaryFiniteSourceFlipCodeOrbit
import ThreeUniformDiaries.DiaryFiniteBoundedUniversality
import ThreeUniformDiaries.DiaryFinitePullbackProtectedEmbedding

/-!
# Explicit protected copy families and feedback on genuine source flips

To prove the second finite diary flip property, the eventual
geometric construction must CONTROL where the protected copies
of the various genuine source flips are placed in a common
finite target B. A bare existential statement, followed by
Classical.choose, does not expose that control.

We therefore use a concrete family of maps, indexed by the
FINITE set of REALISABLE source-flip Boolean edge codes.
Each selected map is accompanied by a genuine bounded full
meet-embedding proof. Given an arbitrary flip T of B, the
canonical induced source pullback along each selected map is
itself a true flip of the corresponding source flip, and
therefore belongs to the same realisable orbit of A.

This gives a well-defined feedback SELF-MAP on the finite
realised orbit, with closure already verified by mathematics.
If that self-map is INJECTIVE under every flip of B, it is
surjective, and an original unflipped A occurs in every flip.
In particular the resulting embedding preserves all mixed
numerical meets and stays inside the finite target bound.

The injectivity condition is explicitly UNPROVED. The point
of this interface is to let a later tree/partite construction
supply deliberate placements, rather than relying on an
uncontrolled proof-selected family or free Boolean split bits.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A CHOSEN protected copy of each actual source flip in a
single finite target B. The map data are explicit, not chosen
implicitly from an existential proof. -/
structure RealizedSourceFlipCopyFamily
    (A B : Ordered3Graph Nat) (n k : Nat) : Type where
  map :
    {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n} → Nat → Nat
  protected :
    ∀ code : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n},
      FiniteBoundedMeetEmbedding
        (finiteDiaryCodeGraph n code.val) B n k (map code)

/-- Given a real protected copy family and a finite target flip
T of B, the canonical pullback code at every source-flip index
belongs to the SAME realisable source orbit. Orbit closure is
a theorem from flip transitivity and exact source pullback. -/
noncomputable def RealizedSourceFlipCopyFamily.feedback
    {A B T : Ordered3Graph Nat} {n k : Nat}
    (C : RealizedSourceFlipCopyFamily A B n k)
    (FT : FiniteDiaryFlip B T k) :
    {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n} →
    {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n} := by
  classical
  intro c
  let P := finiteDiaryCodeGraph n c.val
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c.val).mp c.property
  refine ⟨finiteDiaryEdgeCode
      (finiteDiaryPullbackGraph T n (C.map c)) n, ?_⟩
  change finiteDiaryEdgeCode
      (finiteDiaryPullbackGraph T n (C.map c)) n ∈
      finiteSourceFlipCodes A n
  rw [finiteSourceFlipCodes_eq_of_flip FP]
  exact finiteDiaryPullbackGraph_code_mem_sourceFlips
    FP.target_diary (C.protected c) FT

/-- The feedback really returns the literal code of the complete
induced source pullback, not an imagined free control word. -/
theorem RealizedSourceFlipCopyFamily.feedback_val
    {A B T : Ordered3Graph Nat} {n k : Nat}
    (C : RealizedSourceFlipCopyFamily A B n k)
    (FT : FiniteDiaryFlip B T k)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n}) :
    (C.feedback FT c).val =
      finiteDiaryEdgeCode (finiteDiaryPullbackGraph T n (C.map c)) n := by
  rfl

/-- CONCRETE CONDITIONAL SECOND-FLIP THEOREM:
An explicitly selected family of genuine protected source-flip
copies with injective induced feedback under EVERY target flip
forces the baseline unflipped source to embed into each flip.

No false independent-control assumption enters the proof. -/
theorem RealizedSourceFlipCopyFamily.absorbs_of_feedback_injective
    {A B : Ordered3Graph Nat} {n k : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (C : RealizedSourceFlipCopyFamily A B n k)
    (hInjective : ∀ T : Ordered3Graph Nat,
      ∀ FT : FiniteDiaryFlip B T k,
        Function.Injective (C.feedback FT)) :
    AbsorbsEveryTargetFlipInside A B n k := by
  classical
  intro T FT
  let e := C.feedback FT
  let baseline : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n} :=
    ⟨finiteDiaryEdgeCode A n,
      finiteSourceFlipCodes_baseline_mem DA⟩
  have heSurj : Function.Surjective e :=
    (Finite.injective_iff_surjective).mp (hInjective T FT)
  obtain ⟨c,hc⟩ := heSurj baseline
  let P := finiteDiaryCodeGraph n c.val
  let f := C.map c
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c.val).mp c.property
  have EP : FiniteBoundedMeetEmbedding P B n k f := C.protected c
  have hPullFlip : FiniteDiaryFlip P
      (finiteDiaryPullbackGraph T n f) n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      FP.target_diary EP.toMeetEmbedding EP.image_bound FT
  have hCode :
      finiteDiaryEdgeCode (finiteDiaryPullbackGraph T n f) n =
        finiteDiaryEdgeCode A n := by
    have hVal := congrArg Subtype.val hc
    change (C.feedback FT c).val = finiteDiaryEdgeCode A n at hVal
    exact (C.feedback_val FT c).symm.trans hVal
  have hReconPull : finiteDiaryCodeGraph n
      (finiteDiaryEdgeCode (finiteDiaryPullbackGraph T n f) n) =
        finiteDiaryPullbackGraph T n f :=
    finiteDiaryCodeGraph_reconstruct
      (finiteDiaryPullbackGraph T n f) n
      hPullFlip.target_diary.prediary.frame
  have hReconA : finiteDiaryCodeGraph n
      (finiteDiaryEdgeCode A n) = A :=
    finiteDiaryCodeGraph_reconstruct A n DA.prediary.frame
  have hGraph : finiteDiaryPullbackGraph T n f = A := by
    calc
      finiteDiaryPullbackGraph T n f =
        finiteDiaryCodeGraph n
          (finiteDiaryEdgeCode (finiteDiaryPullbackGraph T n f) n) :=
            hReconPull.symm
      _ = finiteDiaryCodeGraph n (finiteDiaryEdgeCode A n) :=
        congrArg (finiteDiaryCodeGraph n) hCode
      _ = A := hReconA
  have E' : FiniteBoundedMeetEmbedding
      (finiteDiaryPullbackGraph T n f) T n k f :=
    finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
      FP.target_diary EP FT
  refine ⟨f, ?_⟩
  simpa only [hGraph] using E'

/-- Every source has SOME finite target carrying a real,
EXPLICITLY selected protected copy family for all its true
flips. For that family, the remaining sufficient condition
is feedback injectivity on the actual finite source-flip orbit,
not on a fictitious full Boolean cube. -/
theorem exists_universal_target_with_selected_feedback
    (A : Ordered3Graph Nat) (n : Nat)
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ (B : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock B k ∧
      ∃ C : RealizedSourceFlipCopyFamily A B n k,
        (∀ T : Ordered3Graph Nat,
          ∀ FT : FiniteDiaryFlip B T k,
            Function.Injective (C.feedback FT)) →
          AbsorbsEveryTargetFlipInside A B n k := by
  classical
  obtain ⟨B,k,DB,hUniversal⟩ :=
    exists_finiteDiary_for_all_source_flips_bounded A n DA
  have hCopies :
      ∀ c : {code : FiniteDiaryEdgeCode n //
        code ∈ finiteSourceFlipCodes A n},
        ∃ f : Nat → Nat,
          FiniteBoundedMeetEmbedding
            (finiteDiaryCodeGraph n c.val) B n k f := by
    intro c
    have hFlip : FiniteDiaryFlip A (finiteDiaryCodeGraph n c.val) n :=
      (mem_finiteSourceFlipCodes_iff A n c.val).mp c.property
    exact hUniversal (finiteDiaryCodeGraph n c.val) hFlip
  let C : RealizedSourceFlipCopyFamily A B n k := {
    map := fun c => Classical.choose (hCopies c)
    protected := fun c => Classical.choose_spec (hCopies c)
  }
  refine ⟨B,k,DB,C,?_⟩
  intro hInjective
  exact C.absorbs_of_feedback_injective DA hInjective

end DiaryLeafPriority
end ThreeUniformDiaries
