import ThreeUniformDiaries.DiaryLowerUnmarkedRelabellingInvariance
import ThreeUniformDiaries.DiaryLowerCanonicalColourUnavoidability

/-!
# Track C: a persistent canonical colour on UNLABELLED finite A-copies

This result is independent of the exact LABELLED big Ramsey degree
already certified in #1113. The marked-colour lower theorem gives
one colour per pair (finite full diary, genuine full A-marking).
The UNLABELLED colour forgets ONLY this marking; doing so is
well-defined precisely because the previous unmarked-relabelling
invariance theorem proves equality of the full finite diary source
for any two labelled copies occupying the same finite vertex set.

Use a subtype of actual finite A-copies (not all finite subsets) and
the verified canonical marked source; no choice of a preferred
increasing A-presentation or an arbitrary Aut(A) quotient is used.
In every unordered induced U-selfcopy, each genuine UNMARKED finite
diary source appears. This is strictly stronger than just dividing
a labelled palette count by |Aut(A)|.

The existence of an appropriate full diary leaf model U -> K and
the final unlabelled big Ramsey degree upper/lower equivalence
remain separate assembly steps. The circulated manuscript is frozen.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph
open DiaryLeafPriority

/-- Actual UNLABELLED A-copies: exactly the finite vertex sets
realised as images of genuine labelled induced A-embeddings.
For a=0 the only candidate is the empty finite set. -/
abbrev GenuineUnlabelledCopies
    {a : Nat} (A : EnumNode a)
    (U : Ordered3Graph Nat) : Type :=
  { L : Finset Nat // ∃ v : GenuineFiniteEmbeddings A U,
      L = (Finset.univ : Finset (Fin a)).image v.val }

/-- The canonical unmarked finite diary of one actual unlabelled
A-copy. We select any genuine labelled witness, then FORGET its
marked positions. The preceding relabelling-invariance theorem
shows that the result is independent of this choice. -/
noncomputable def canonicalUnmarkedDiaryColour
    {U K : Ordered3Graph Nat} (D : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ u : Nat, IsLeaf K (F u))
    {a : Nat} (A : EnumNode a) :
    GenuineUnlabelledCopies A U →
      ↑(allGenuineUnmarkedDiarySources A) :=
  fun L => by
    classical
    let v : GenuineFiniteEmbeddings A U :=
      Classical.choose L.property
    let d : GenuineMarkedDiaryTypes A :=
      canonicalMarkedDiaryColour D F hFLeaf A v
    refine ⟨d.val.source, ?_⟩
    change d.val.source ∈
      (allGenuineMarkedDiaryFinset A).image
        (fun T => T.source)
    exact Finset.mem_image.mpr ⟨d.val, d.property, rfl⟩

/-- Source of the unlabelled colouring agrees with the canonical
marked colour of ANY genuine labelled representative, even if its
labels occur in a different numerical order from the chosen
witness in the definition. This eliminates any hidden choice. -/
theorem canonicalUnmarkedDiaryColour_eq_source
    {U K : Ordered3Graph Nat} (D : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ u : Nat, IsLeaf K (F u))
    {a : Nat} (A : EnumNode a)
    (L : GenuineUnlabelledCopies A U)
    (v : GenuineFiniteEmbeddings A U)
    (hL : L.val =
      (Finset.univ : Finset (Fin a)).image v.val) :
    (canonicalUnmarkedDiaryColour D F hFLeaf A L).val =
      (canonicalMarkedDiaryColour D F hFLeaf A v).val.source := by
  classical
  let z : GenuineFiniteEmbeddings A U :=
    Classical.choose L.property
  have hz :
      L.val = (Finset.univ : Finset (Fin a)).image z.val :=
    Classical.choose_spec L.property
  have hRange :
      (Finset.univ : Finset (Fin a)).image z.val =
        (Finset.univ : Finset (Fin a)).image v.val :=
    hz.symm.trans hL
  change (canonicalMarkedDiaryColour D F hFLeaf A z).val.source =
    (canonicalMarkedDiaryColour D F hFLeaf A v).val.source
  exact canonicalMarkedDiaryColour_source_eq_of_same_range
    D F hFLeaf A z v hRange

/-- Under an arbitrary unordered induced universal selfcopy,
EVERY true unmarked finite diary source occurs as the
canonical colour of an actual unlabelled A-copy. This is a
genuine geometric statement and uses the already kernel-checked
marked-colour unavoidability, not an assumption of unmarked
surjectivity or the stronger countable diary theorem. -/
theorem canonicalUnmarkedDiaryColour_unavoidable
    (G : GenericEnumerated3Graph)
    (U K : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (D : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ u : Nat, IsLeaf K (F u))
    {a : Nat} (A : EnumNode a) :
    ∀ (w : UnorderedEmbedding U U)
      (d : ↑(allGenuineUnmarkedDiarySources A)),
      ∃ v : GenuineFiniteEmbeddings A U,
        canonicalUnmarkedDiaryColour D F hFLeaf A
          ⟨(Finset.univ : Finset (Fin a)).image (v.postcompose w).val,
           ⟨v.postcompose w, rfl⟩⟩ = d := by
  classical
  intro w d
  have hd : d.val ∈
      (allGenuineMarkedDiaryFinset A).image (fun T => T.source) :=
    d.property
  obtain ⟨T, hT, hSource⟩ := Finset.mem_image.mp hd
  let dm : GenuineMarkedDiaryTypes A := ⟨T, hT⟩
  obtain ⟨v, hv⟩ :=
    (canonicalMarkedDiaryColour_unavoidable
      G U K hUniversal D F hFLeaf A) w dm
  refine ⟨v, ?_⟩
  apply Subtype.ext
  have hSourceColour :=
    canonicalUnmarkedDiaryColour_eq_source
      D F hFLeaf A
      (⟨(Finset.univ : Finset (Fin a)).image (v.postcompose w).val,
         ⟨v.postcompose w, rfl⟩⟩ :
         GenuineUnlabelledCopies A U)
      (v.postcompose w) rfl
  calc
    (canonicalUnmarkedDiaryColour D F hFLeaf A
      ⟨(Finset.univ : Finset (Fin a)).image (v.postcompose w).val,
       ⟨v.postcompose w, rfl⟩⟩).val =
        (canonicalMarkedDiaryColour D F hFLeaf A
          (v.postcompose w)).val.source := hSourceColour
    _ = dm.val.source :=
      congrArg (fun q : GenuineMarkedDiaryTypes A => q.val.source) hv
    _ = d.val := hSource

end ATRFiniteDecoder
end ThreeUniformDiaries
