import ThreeUniformDiaries.DiaryLowerCanonicalMarkedColour
import ThreeUniformDiaries.DiaryFiniteMeetLabelledCopyTransport
import ThreeUniformDiaries.DiaryFiniteUniversalLeafRange

/-!
# Track C lower: every genuine marked diary colour persists in every self-copy

The candidate colour was already defined on ACTUAL induced labelled
A-embeddings in merged #1102, and is unique from exact support,
graph and labelled indices. The finite universal leaf-range theorem
supplies an ACTUAL full finite meet embedding of every genuine marked
source in the image of any prescribed unordered universal copy.

This module combines these genuinely proved ingredients. For each
ambient selfembedding w and each marked diary source d:
* choose actual preimages of all source marked leaves under F ∘ w;
* use six-permutation full finite meet transport and unordered
  reflection to get a genuine induced labelled A-copy;
* show the selected image leaves generate EXACTLY g[range n];
* use sorted support index, literal finite EnumNode recovery and
  exact labelled ranks to identify the canonical marked source
  with d, not just an unlabelled-isomorphic diary.

The theorem quantifies over a given full diary leaf model U→K and
a given enumerated generic graph G. Eliminating those parameters
via checked countable diary and generic existence theorems is
a separate routine assembly. No extra countable full-diary
unavoidability or hypothetical colouring-persistence premise
is assumed.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph
open DiaryLeafPriority

/-- Induced labelled A-copies are also REFLECTED by an unordered
induced hypergraph embedding. The existing Track A lemma gives
the forward implication, while the reverse uses injectivity
and reflection of every distinct unordered triple. -/
theorem isInducedLabelledCopy_of_map_unordered
    {a : Nat} (A : EnumNode a)
    {U K : Ordered3Graph Nat}
    (F : UnorderedEmbedding U K)
    (v : Fin a → Nat)
    (hCopy : IsInducedLabelledCopy A K (fun i => F (v i))) :
    IsInducedLabelledCopy A U v := by
  refine ⟨?_, ?_⟩
  · intro i j h
    apply hCopy.1
    exact congrArg F h
  · intro i j k hij hjk
    have hDistinctIJ : v i ≠ v j := by
      intro h
      exact (ne_of_lt hij) (hCopy.1 (congrArg F h))
    have hDistinctIK : v i ≠ v k := by
      intro h
      exact (ne_of_lt (lt_trans hij hjk))
        (hCopy.1 (congrArg F h))
    have hDistinctJK : v j ≠ v k := by
      intro h
      exact (ne_of_lt hjk) (hCopy.1 (congrArg F h))
    exact (hCopy.2 i j k hij hjk).trans
      (F.edge_iff_distinct (v i) (v j) (v k)
        hDistinctIJ hDistinctIK hDistinctJK).symm

/-- The total canonical marked-diary colouring is genuinely
UNAVOIDABLE: each true marked full diary colour appears among
actual labelled A-embeddings in the image of EACH arbitrary
unordered induced selfembedding of the countably universal U.

This proof uses the *finite* full-diary unavoidability theorem.
In particular it does not assume the stronger countable-source
diary unavoidability theorem from the circulation manuscript.
-/
theorem canonicalMarkedDiaryColour_unavoidable
    (G : GenericEnumerated3Graph)
    (U K : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a : Nat} (A : EnumNode a) :
    IsEveryMarkedDiaryColourUnavoidable A U
      (canonicalMarkedDiaryColour DK F hFLeaf A) := by
  classical
  intro w d
  let Q : MarkedFiniteSource 0 a := d.val
  let H : Ordered3Graph Nat := Q.source.picture.toOrdered3Graph
  let n : Nat := Q.source.k + 1
  have hShape : IsGenuineMarkedDiaryShape A Q :=
    (mem_allGenuineMarkedDiaryFinset_iff A Q).mp d.property
  obtain ⟨DSource, hSourceCopy, hMarkedLeaves, hCover⟩ := hShape
  let Fw : UnorderedEmbedding U K := F.comp w
  have hFwLeaf : ∀ u : Nat, IsLeaf K (Fw u) := by
    intro u
    exact hFLeaf (w u)
  obtain ⟨g, E, hRange⟩ :=
    exists_finiteDiary_full_embedding_in_universal_leaf_range
      DSource G hUniversal Fw hFwLeaf DK

  -- Choose one ACTUAL inverse image of each marked source leaf.
  let hPre (i : Fin a) :
      ∃ t : Nat, g (Q.marked i).val = Fw t :=
    hRange (Q.marked i).val
      (hMarkedLeaves i).1 (Q.marked i).isLt (hMarkedLeaves i)
  let t : Fin a → Nat := fun i => Classical.choose (hPre i)
  have hImages (i : Fin a) :
      g (Q.marked i).val = Fw (t i) :=
    Classical.choose_spec (hPre i)

  have hCopyImage :
      IsFiniteLabelledCopy A.toOrdered3Graph K a
        (fun i => g (Q.marked i).val) :=
    (E.labelledCopy_iff A.toOrdered3Graph a Q.marked).mp
      hSourceCopy
  have hCopyFw :
      IsFiniteLabelledCopy A.toOrdered3Graph K a
        (fun i => Fw (t i)) := by
    have hfuns :
        (fun i : Fin a => g (Q.marked i).val) =
          (fun i : Fin a => Fw (t i)) := by
      funext i
      exact hImages i
    rw [← hfuns]
    exact hCopyImage
  have hCopyK :
      IsInducedLabelledCopy A K (fun i => Fw (t i)) :=
    (isInducedLabelledCopy_iff_fullUnordered
      A K (fun i => Fw (t i))).mpr hCopyFw
  have hCopyU : IsInducedLabelledCopy A U t :=
    isInducedLabelledCopy_of_map_unordered A Fw t hCopyK
  let v : GenuineFiniteEmbeddings A U := ⟨t, hCopyU⟩

  -- The marked source positions exhaust ALL true source leaves.
  let L : Finset Nat :=
    (Finset.univ : Finset (Fin a)).image
      (fun i => (Q.marked i).val)
  have hL (u : Nat) : u ∈ L ↔
      3 ≤ u ∧ u < n ∧ IsLeaf H u := by
    constructor
    · intro hu
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
      exact ⟨(hMarkedLeaves i).1,
        (Q.marked i).isLt, hMarkedLeaves i⟩
    · rintro ⟨hu3,hun,hLeaf⟩
      obtain ⟨i,hi⟩ := hCover u hu3 hun hLeaf
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

  let q : Fin a → Nat := fun i => Fw (t i)
  let Lq : Finset Nat :=
    (Finset.univ : Finset (Fin a)).image q
  have hLeavesQ : ∀ i : Fin a, IsLeaf K (q i) :=
    fun i => hFwLeaf (t i)
  have hCopyQ : IsInducedLabelledCopy A K q := hCopyK
  have hLq : Lq = L.image g := by
    calc
      Lq = (Finset.univ : Finset (Fin a)).image
          (fun i => g (Q.marked i).val) := by
        apply Finset.image_congr
        intro i _
        exact (hImages i).symm
      _ = L.image g := by
        simp only [L, Finset.image_image, Function.comp_def]
        rfl

  let S : Finset Nat := finiteLeafMeetSupport K (L.image g)
  obtain ⟨hCard, hIndex⟩ :=
    E.canonical_leafSupport_card_and_index DSource L hL
  have hActualImageLeaves :
      ∀ u : Nat, u ∈ L.image g → IsLeaf K u := by
    intro u hu
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hx3,hxn,hLeaf⟩ := (hL x).mp hx
    exact (E.leaf_iff x hx3 hxn).mpr hLeaf
  have hFullCompressed :
      FiniteRoleDiaryBlock (finiteSupportGraph K S) S.card :=
    finiteLeafMeetSupport_is_finiteDiary DK hActualImageLeaves
  have hTargetZeroExtension :
      ((finiteSupportGraph K S).initialSegment S.card).toOrdered3Graph =
        finiteSupportGraph K S :=
    hFullCompressed.zeroExtended_source_eq
  have hExactEnum :
      (finiteSupportGraph K S).initialSegment n = Q.source.picture :=
    E.canonical_leafSupport_sourcePicture_eq
      Q.source.picture DSource L hL
  have hExactGraph :
      Q.source.picture.toOrdered3Graph = finiteSupportGraph K S := by
    calc
      Q.source.picture.toOrdered3Graph =
          ((finiteSupportGraph K S).initialSegment n).toOrdered3Graph :=
        congrArg EnumNode.toOrdered3Graph hExactEnum.symm
      _ = ((finiteSupportGraph K S).initialSegment S.card).toOrdered3Graph := by
        rw [hCard]
      _ = finiteSupportGraph K S := hTargetZeroExtension

  have hSizeQ :
      Q.source.k + 1 = (finiteLeafMeetSupport K Lq).card := by
    change n = (finiteLeafMeetSupport K Lq).card
    rw [hLq]
    exact hCard.symm
  have hGraphQ :
      Q.source.picture.toOrdered3Graph =
        finiteSupportGraph K (finiteLeafMeetSupport K Lq) := by
    rw [hLq]
    exact hExactGraph
  have hIndicesQ : ∀ i : Fin a,
      finiteSupportIndex (finiteLeafMeetSupport K Lq)
        (Q.marked i).val = q i := by
    intro i
    rw [hLq]
    exact (hIndex (Q.marked i).val (Q.marked i).isLt).trans
      (hImages i)
  have hCanon :
      canonicalMarkedSourceOfLeaves DK A q hLeavesQ hCopyQ = Q :=
    canonicalMarkedSourceOfLeaves_eq_of_spec
      DK A q hLeavesQ hCopyQ Q hSizeQ hGraphQ hIndicesQ
  refine ⟨v, ?_⟩
  apply Subtype.ext
  change canonicalMarkedSourceOfLeaves DK A q hLeavesQ hCopyQ = Q
  exact hCanon

end ATRFiniteDecoder
end ThreeUniformDiaries
