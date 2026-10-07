import Mathlib

/-!
# One-types, auxiliary two-types, and type-respecting maps

This file formalizes the elementary decomposition used after the repaired
aux-type Ramsey theorem in the 3-uniform diaries manuscript.

We work with ordered ternary edge predicates.  The manuscript only evaluates
the edge relation on increasing triples, so symmetry is not built into the
structure here.
-/

namespace ThreeUniformDiaries

universe u v

/-- An ordered 3-uniform hypergraph presented by its increasing-triple edge
predicate. -/
structure Ordered3Graph (α : Type u) where
  edge : α → α → α → Prop

namespace Ordered3Graph

variable {α : Type u} {β : Type v}
variable [LinearOrder α] [LinearOrder β]

/-- Equality of singleton types below the cut `l`. -/
def SameOneTypeBelow (H : Ordered3Graph α) (l u v : α) : Prop :=
  ∀ ⦃a b : α⦄, a < b → b < l →
    (H.edge a b u ↔ H.edge a b v)

/-- Equality of the auxiliary type of two ordered pairs below the cut `l`.
Only edges containing both members of the pair are recorded. -/
def SameAuxTypeBelow (H : Ordered3Graph α)
    (l u₀ u₁ v₀ v₁ : α) : Prop :=
  ∀ ⦃a : α⦄, a < l →
    (H.edge a u₀ u₁ ↔ H.edge a v₀ v₁)

/-- Equality of two ordered 2-types below `l`.

For a ternary relation this is exactly the conjunction of the two coordinate
1-types and the auxiliary type of the pair. -/
def SameTwoTypeBelow (H : Ordered3Graph α)
    (l u₀ u₁ v₀ v₁ : α) : Prop :=
  H.SameOneTypeBelow l u₀ v₀ ∧
  H.SameOneTypeBelow l u₁ v₁ ∧
  H.SameAuxTypeBelow l u₀ u₁ v₀ v₁

theorem sameTwoTypeBelow_iff (H : Ordered3Graph α)
    (l u₀ u₁ v₀ v₁ : α) :
    H.SameTwoTypeBelow l u₀ u₁ v₀ v₁ ↔
      H.SameOneTypeBelow l u₀ v₀ ∧
      H.SameOneTypeBelow l u₁ v₁ ∧
      H.SameAuxTypeBelow l u₀ u₁ v₀ v₁ :=
  Iff.rfl

/-- An order-preserving induced embedding. -/
structure Embedding (H : Ordered3Graph α) (K : Ordered3Graph β) where
  toFun : α → β
  strictMono : StrictMono toFun
  edge_iff :
    ∀ ⦃a b c : α⦄, a < b → b < c →
      (H.edge a b c ↔ K.edge (toFun a) (toFun b) (toFun c))

namespace Embedding

variable {H : Ordered3Graph α} {K : Ordered3Graph β}

instance : CoeFun (Embedding H K) (fun _ => α → β) :=
  ⟨Embedding.toFun⟩

/-- Preservation and reflection of singleton-type equality at corresponding
cuts.  This is the relation-level version of preserving singleton meets. -/
def PreservesOneTypes (f : Embedding H K) : Prop :=
  ∀ l u v, l ≤ u → l ≤ v →
    H.SameOneTypeBelow l u v ↔
      K.SameOneTypeBelow (f l) (f u) (f v)

/-- Preservation and reflection of auxiliary-type equality at corresponding
cuts.  Only ordered pairs lying above the cut occur in the manuscript. -/
def PreservesAuxTypes (f : Embedding H K) : Prop :=
  ∀ l u₀ u₁ v₀ v₁,
    l ≤ u₀ → u₀ < u₁ → l ≤ v₀ → v₀ < v₁ →
    H.SameAuxTypeBelow l u₀ u₁ v₀ v₁ ↔
      K.SameAuxTypeBelow (f l) (f u₀) (f u₁) (f v₀) (f v₁)

/-- Preservation and reflection of ordinary 2-type equality at corresponding
cuts, for ordered pairs above the cut. -/
def PreservesTwoTypes (f : Embedding H K) : Prop :=
  ∀ l u₀ u₁ v₀ v₁,
    l ≤ u₀ → u₀ < u₁ → l ≤ v₀ → v₀ < v₁ →
    H.SameTwoTypeBelow l u₀ u₁ v₀ v₁ ↔
      K.SameTwoTypeBelow (f l) (f u₀) (f u₁) (f v₀) (f v₁)

/-- The relation-level form of an aux-type-respecting embedding. -/
structure AuxTypeRespecting (f : Embedding H K) : Prop where
  one : f.PreservesOneTypes
  aux : f.PreservesAuxTypes

/-- The relation-level form of a type-respecting embedding. -/
structure TypeRespecting (f : Embedding H K) : Prop where
  one : f.PreservesOneTypes
  two : f.PreservesTwoTypes

/-- The manuscript identity saying that an ordinary 2-type is determined by
the two singleton types and the auxiliary type.  Consequently every
aux-type-respecting embedding is type-respecting. -/
theorem AuxTypeRespecting.typeRespecting
    {f : Embedding H K} (hf : f.AuxTypeRespecting) :
    f.TypeRespecting := by
  refine ⟨hf.one, ?_⟩
  intro l u₀ u₁ v₀ v₁ hlu hu hlv hv
  have hlu₁ : l ≤ u₁ := hlu.trans hu.le
  have hlv₁ : l ≤ v₁ := hlv.trans hv.le
  simp only [SameTwoTypeBelow]
  rw [hf.one l u₀ v₀ hlu hlv,
    hf.one l u₁ v₁ hlu₁ hlv₁,
    hf.aux l u₀ u₁ v₀ v₁ hlu hu hlv hv]

end Embedding
end Ordered3Graph
end ThreeUniformDiaries
