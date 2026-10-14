import ThreeUniformDiaries.DiaryFiniteSingletonEnvelope
import ThreeUniformDiaries.DiaryFinitePointedEnumNode
import ThreeUniformDiaries.DiaryFinitePointedRamsey

/-!
# Singleton envelopes as actual finite ATR sources

The finite n+1-vertex singleton envelope already preserves every
one-type and auxiliary pair-type meet on its real vertices. This file
converts those exact meet equalities into finite cut-by-cut type
reflection and constructs the genuine extensional
`FiniteAuxEmbeddingImage` of its zero-extended `EnumNode (n+1)`.

The verified unconditional finite ATR theorem then homogenises ALL
prefix-fixed finite copies of this singleton shape, preserving its
canonical terminal vertex. This does not colour the artificial
continuation of the finite source.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace FiniteSingletonEnvelope

variable {K : Ordered3Graph Nat} {n a : Nat}

/-- Singleton type equality at every real cut of a one-tail envelope
agrees exactly with the ambient target type, including skipped
target indices. -/
theorem one_cut_iff
    (E : FiniteSingletonEnvelope K n a)
    (w u v : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hu : u < n+1) (hv : v < n+1) :
    E.induced.SameOneTypeBelow w u v ↔
      K.SameOneTypeBelow (E.enumerate w)
        (E.enumerate u) (E.enumerate v) := by
  have hsource :=
    E.induced.oneMeetLevel_ge_iff_sameOneTypeBelow w u v hwu hwv
  have htarget :=
    K.oneMeetLevel_ge_iff_sameOneTypeBelow
      (E.enumerate w) (E.enumerate u) (E.enumerate v)
      (E.strictMono.monotone hwu)
      (E.strictMono.monotone hwv)
  constructor
  · intro hs
    apply htarget.mp
    rw [E.singleton_meets u v hu hv]
    exact E.strictMono.monotone (hsource.mpr hs)
  · intro ht
    apply hsource.mp
    have he := htarget.mpr ht
    rw [E.singleton_meets u v hu hv] at he
    by_contra hn
    have hlt : E.induced.oneMeetLevel u v < w := by omega
    have hmono := E.strictMono hlt
    have hle : E.enumerate w ≤
        E.enumerate (E.induced.oneMeetLevel u v) := by
      simpa only [induced] using he
    exact (not_lt_of_ge hle) hmono

/-- The analogous equivalence for auxiliary 2-types on real
ordered pairs within the one-tail envelope. -/
theorem aux_cut_iff
    (E : FiniteSingletonEnvelope K n a)
    (w u v x y : Nat)
    (hwu : w ≤ u) (huv : u < v)
    (hwx : w ≤ x) (hxy : x < y)
    (hv : v < n+1) (hy : y < n+1) :
    E.induced.SameAuxTypeBelow w u v x y ↔
      K.SameAuxTypeBelow (E.enumerate w)
        (E.enumerate u) (E.enumerate v)
        (E.enumerate x) (E.enumerate y) := by
  have hsource :=
    E.induced.auxMeetLevel_ge_iff_sameAuxTypeBelow
      w u v x y hwu hwx
  have htarget :=
    K.auxMeetLevel_ge_iff_sameAuxTypeBelow
      (E.enumerate w) (E.enumerate u) (E.enumerate v)
      (E.enumerate x) (E.enumerate y)
      (E.strictMono.monotone hwu)
      (E.strictMono.monotone hwx)
  constructor
  · intro hs
    apply htarget.mp
    rw [E.auxiliary_meets u v x y huv hxy hv hy]
    exact E.strictMono.monotone (hsource.mpr hs)
  · intro ht
    apply hsource.mp
    have he := htarget.mpr ht
    rw [E.auxiliary_meets u v x y huv hxy hv hy] at he
    by_contra hn
    have hlt : E.induced.auxMeetLevel u v x y < w := by omega
    have hmono := E.strictMono hlt
    have hle : E.enumerate w ≤
        E.enumerate (E.induced.auxMeetLevel u v x y) := by
      simpa only [induced] using he
    exact (not_lt_of_ge hle) hmono

/-- A native singleton-envelope inclusion satisfies all finite
auxiliary embedding conditions on exactly n+1 real vertices. -/
theorem finite_aux_embedding
    (E : FiniteSingletonEnvelope K n a) :
    FiniteAuxEmbedding E.induced K E.enumerate (n+1) := by
  refine ⟨E.strictMono, ?_, ?_, ?_⟩
  · intro u v w huv hvw hw
    exact Iff.rfl
  · intro w u v hwu hwv hu hv
    exact E.one_cut_iff w u v hwu hwv hu hv
  · intro w u v x y hwu huv hwx hxy hv hy
    exact E.aux_cut_iff w u v x y hwu huv hwx hxy hv hy

/-- The native `EnumNode` containing precisely the n+1 vertices
of a singleton envelope. -/
noncomputable def finiteEnum
    (E : FiniteSingletonEnvelope K n a) : EnumNode (n+1) :=
  E.induced.initialSegment (n+1)

/-- Genuine extensional ATR code of the finite singleton inclusion.
Only the images of the first n+1 vertices are colouring data. -/
noncomputable def finiteATRCode
    (E : FiniteSingletonEnvelope K n a) :
    FiniteAuxEmbeddingImage E.finiteEnum.toOrdered3Graph K (n+1) :=
  FiniteAuxEmbeddingImage.ofFiniteAuxEmbedding E.enumerate
    E.finite_aux_embedding.of_initialSegment

theorem finiteATRCode_fix_prefix
    (E : FiniteSingletonEnvelope K n a)
    (i : Fin (n+1)) (hi : i.val < n) :
    E.finiteATRCode.image i = i.val := by
  change E.enumerate i.val = i.val
  exact E.protected_prefix i.val hi

theorem finiteATRCode_last
    (E : FiniteSingletonEnvelope K n a) :
    E.finiteATRCode.image ⟨n, Nat.lt_succ_self n⟩ = a := by
  change E.enumerate n = a
  exact E.endpoint

end FiniteSingletonEnvelope
end Ordered3Graph

namespace Ordered3Graph
namespace FiniteSingletonEnvelope

/-- Unconditional ATR homogeneity of all genuine finite copies
of a given singleton envelope over its fixed protected prefix. -/
theorem ramsey_for_fixed_prefix
    (G : GenericEnumerated3Graph)
    {n a : Nat} (E : FiniteSingletonEnvelope G.graph n a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : FiniteAuxEmbeddingImage E.finiteEnum.toOrdered3Graph
      G.graph (n+1) → κ) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
        (∀ t < n, u t = t) ∧
        ∃ color : κ,
          ∀ e : FiniteAuxEmbeddingImage
              E.finiteEnum.toOrdered3Graph G.graph (n+1),
            (∀ i : Fin (n+1), i.val < n → e.image i = i.val) →
            χ (e.postcompose u hu) = color := by
  exact ATRFiniteDecoder.actualFiniteAuxRamsey_positiveSize
    G (n := n) (m := n+1)
    (Nat.le_succ n) (Nat.zero_lt_succ n)
    E.finiteEnum χ

/-- The canonical singleton copy participates in the homogeneous
colour and its last real finite vertex remains distinguished. -/
theorem ramsey_colour_on_canonical_copy
    (G : GenericEnumerated3Graph)
    {n a : Nat} (E : FiniteSingletonEnvelope G.graph n a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : FiniteAuxEmbeddingImage E.finiteEnum.toOrdered3Graph
      G.graph (n+1) → κ) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
        (∀ t < n, u t = t) ∧
        ∃ color : κ,
          χ (E.finiteATRCode.postcompose u hu) = color ∧
          ∀ e : FiniteAuxEmbeddingImage
              E.finiteEnum.toOrdered3Graph G.graph (n+1),
            (∀ i : Fin (n+1), i.val < n → e.image i = i.val) →
            χ (e.postcompose u hu) = color := by
  obtain ⟨u, hu, hfix, color, hcol⟩ :=
    E.ramsey_for_fixed_prefix G χ
  refine ⟨u, hu, hfix, color, ?_, hcol⟩
  exact hcol E.finiteATRCode E.finiteATRCode_fix_prefix

end FiniteSingletonEnvelope
end Ordered3Graph
end ThreeUniformDiaries
