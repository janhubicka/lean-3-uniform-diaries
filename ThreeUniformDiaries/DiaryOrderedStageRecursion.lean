import ThreeUniformDiaries.DiaryCompleteFiniteStage
import ThreeUniformDiaries.DiaryFusionStabilisation

/-!
# Recursive complete finite stages and order-preserving fused image

At the kth stage of the lower-bound type stabilisation argument, the
ambient outer map F need only be injective. The induction maintains
a genuine aux-type-respecting embedding g_k whose outer image F∘g_k
is increasing on the first k+1 source vertices.

The complete one-cut ATR stage applied at n=k+1 gives a
prefix-fixing refinement h, preserving earlier images and
stabilising ALL native small-envelope finite colours. We record
the selected refinement as proof data and recursively form
g_(k+1)=g_k∘h.

The resulting embeddings are prefix-stable. The already verified
countable-fusion theorem yields an aux-type-respecting embedding
g with F∘g strictly increasing on ALL of Nat, thereby formalising
the order-preservation conclusion (I1) of the diary lower-bound
type-stabilisation lemma.

The recorded finite stage colour invariants still need to be
translated into the quantified singleton and pointed-pair
conclusions (I2) and (I3). No such conclusion is assumed here.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- At stage k the external image is already increasing on the
first k+1 vertices. -/
structure OrderedDiaryStage
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (F : Nat → Nat) (k : Nat) where
  map : Embedding G.graph G.graph
  aux : map.AuxTypeRespecting
  increasing_prefix :
    ∀ a b, a < b → b < k+1 → F (map a) < F (map b)

namespace OrderedDiaryStage

variable {G : GenericEnumerated3Graph}
  {K : Ordered3Graph Nat} {F : Nat → Nat} {k : Nat}

/-- A complete stabilising refinement at the next cut k+1.
Its finite type and orientation colours are retained explicitly
for later proof of (I2) and (I3). -/
structure Refinement (S : OrderedDiaryStage G K F k) where
  embedding : Embedding G.graph G.graph
  aux : embedding.AuxTypeRespecting
  fixes_prefix : ∀ t < k+1, embedding t = t
  next_increasing :
    ∀ a b, a < b → b < k+2 →
      F (S.map (embedding a)) < F (S.map (embedding b))
  tail_avoids :
    ∀ a, k+1 ≤ a →
      F (S.map k) < F (S.map (embedding a))
  full_colours :
    ∀ A ∈ smallSourceUniverse (k+1),
      ∃ color : FullEnvelopeColour (F (S.map k)+1),
        ∀ e : A.Code G, A.FixesPrefix G e →
          fullEnvelopeColour K (fun v => F (S.map v))
            (F (S.map k)+1) A
            (e.postcompose embedding aux) = color

/-- The verified complete finite stage produces a concrete
prefix-fixing refinement with all the stated records. -/
noncomputable def chooseRefinement
    (S : OrderedDiaryStage G K F k)
    (hF : Function.Injective F) :
    S.Refinement := by
  let F' : Nat → Nat := fun v => F (S.map v)
  have hF' : Function.Injective F' :=
    hF.comp S.map.strictMono.injective
  have hp : ∀ a b, a < b → b < k+1 → F' a < F' b :=
    S.increasing_prefix
  classical
  have hexists : Nonempty (S.Refinement) := by
    obtain ⟨h, hh, hfix, horder, havoid, hcolors⟩ :=
      actualFiniteAuxRamsey_extendOrderedPrefix
        G (k+1) (by omega) K F' hF' hp (F' k + 1)
    refine ⟨{
      embedding := h
      aux := hh
      fixes_prefix := hfix
      next_increasing := ?_
      tail_avoids := havoid
      full_colours := hcolors
    }⟩
    intro a b hab hb
    exact horder a b hab (by omega)
  exact Classical.choice hexists

/-- Form the next stage by composing the present embedding on the
right with its protected finite ATR refinement. -/
def next (S : OrderedDiaryStage G K F k)
    (R : S.Refinement) :
    OrderedDiaryStage G K F (k+1) := by
  refine {
    map := S.map.comp R.embedding
    aux := S.aux.comp R.aux
    increasing_prefix := ?_
  }
  intro a b hab hb
  change F (S.map (R.embedding a)) <
    F (S.map (R.embedding b))
  exact R.next_increasing a b hab (by omega)

/-- Initial stage: the identity embedding. An arbitrary outer map
is vacuously increasing on the first singleton prefix. -/
def initial
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat) (F : Nat → Nat) :
    OrderedDiaryStage G K F 0 := by
  let e : Embedding G.graph G.graph := {
    toFun := id
    strictMono := by
      intro a b hab
      exact hab
    edge_iff := by
      intro a b c hab hbc
      exact Iff.rfl
  }
  have he : e.AuxTypeRespecting := by
    constructor
    · intro l a b hla hlb
      exact Iff.rfl
    · intro l a b c d hla hab hlc hcd
      exact Iff.rfl
  refine ⟨e, he, ?_⟩
  intro a b hab hb
  omega

end OrderedDiaryStage

/-- The recursively selected complete finite stages. The
refinement at step k is made at cut k+1, hence fixes all
previously chosen images of the first k+1 vertices. -/
noncomputable def orderedDiaryStages
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F) :
    (k : Nat) → OrderedDiaryStage G K F k
  | 0 => OrderedDiaryStage.initial G K F
  | k+1 =>
      let S := orderedDiaryStages G K F hF k
      S.next (S.chooseRefinement hF)

/-- The actual induced aux-type-respecting self-embedding at
stage k. -/
noncomputable def orderedDiaryEmbeddings
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (k : Nat) : Embedding G.graph G.graph :=
  (orderedDiaryStages G K F hF k).map

theorem orderedDiaryStages_succ
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (k : Nat) :
    orderedDiaryStages G K F hF (k+1) =
      (orderedDiaryStages G K F hF k).next
        ((orderedDiaryStages G K F hF k).chooseRefinement hF) :=
  rfl

/-- Later stages do not change earlier source vertices. -/
theorem orderedDiaryEmbeddings_prefixStable
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F) :
    Embedding.PrefixStable (orderedDiaryEmbeddings G K F hF) := by
  intro k t htk
  have hfix := ((orderedDiaryStages G K F hF k).chooseRefinement
    hF).fixes_prefix t (by omega)
  change (orderedDiaryStages G K F hF (k+1)).map t =
    (orderedDiaryStages G K F hF k).map t
  rw [orderedDiaryStages_succ]
  change (orderedDiaryStages G K F hF k).map
      (((orderedDiaryStages G K F hF k).chooseRefinement hF).embedding t) =
    (orderedDiaryStages G K F hF k).map t
  rw [hfix]

/-- Every finite stage is aux-type-respecting. -/
theorem orderedDiaryEmbeddings_aux
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F) (k : Nat) :
    (orderedDiaryEmbeddings G K F hF k).AuxTypeRespecting :=
  (orderedDiaryStages G K F hF k).aux

/-- At stage k the outer image of the first k+1 vertices is
strictly increasing. -/
theorem orderedDiaryEmbeddings_increasingPrefix
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (k a b : Nat) (hab : a < b) (hb : b < k+1) :
    F (orderedDiaryEmbeddings G K F hF k a) <
      F (orderedDiaryEmbeddings G K F hF k b) :=
  (orderedDiaryStages G K F hF k).increasing_prefix a b hab hb

/-- Condition (I1) of the type-stabilisation lemma: every
injective outer map becomes order-preserving on the image
of one aux-type-respecting generic self-embedding.

The proof is a genuine recursive ATR construction followed by
the already checked prefix-stable fusion theorem. -/
theorem exists_auxEmbedding_ordering_outer_injection
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F) :
    ∃ g : Embedding G.graph G.graph,
      g.AuxTypeRespecting ∧
      StrictMono (fun t => F (g t)) := by
  let stages := orderedDiaryEmbeddings G K F hF
  have hs : Embedding.PrefixStable stages :=
    orderedDiaryEmbeddings_prefixStable G K F hF
  let g := Embedding.fusionEmbedding stages hs
  have hg : g.AuxTypeRespecting :=
    Embedding.fusionEmbedding_auxTypeRespecting stages hs
      (orderedDiaryEmbeddings_aux G K F hF)
  have horder : StrictMono (fun t => F (g t)) := by
    apply Embedding.fusion_order_preserved F stages hs
    intro k a b hab hb
    exact orderedDiaryEmbeddings_increasingPrefix
      G K F hF k a b hab (by omega)
  exact ⟨g, hg, horder⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
