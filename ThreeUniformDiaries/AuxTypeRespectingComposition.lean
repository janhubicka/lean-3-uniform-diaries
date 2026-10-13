import ThreeUniformDiaries.AuxTypes

/-!
# Composition of genuine aux-type-respecting hypergraph embeddings

The final ATR Ramsey argument composes the canonical finite source
embedding A -> H with the single uniform universal-branch embedding
H -> G. The induced-edge and one/auxiliary-type conditions must
survive this composition, in BOTH directions, not just as
homomorphism implications.

This is the exact relation-level composition theorem for the
manuscript's Embedding/AuxTypeRespecting definitions. No category
theory, stronger types, or unproved Ramsey input is used.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace Embedding

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]
variable {H : Ordered3Graph α} {K : Ordered3Graph β}
  {L : Ordered3Graph γ}

/-- Composition of strictly increasing induced embeddings, with the
exact iff for every increasing ternary edge. -/
def comp (g : Embedding K L) (f : Embedding H K) :
    Embedding H L where
  toFun := fun a => g (f a)
  strictMono := g.strictMono.comp f.strictMono
  edge_iff := by
    intro a b c hab hbc
    exact (f.edge_iff hab hbc).trans
      (g.edge_iff (f.strictMono hab) (f.strictMono hbc))

@[simp] theorem comp_apply
    (g : Embedding K L) (f : Embedding H K) (a : α) :
    (g.comp f) a = g (f a) := rfl

/-- Auxiliary-type preservation and reflection are stable under
composition, including the singleton-type equalities and the
two ordered-pair auxiliary-type equalities at every cut. -/
theorem AuxTypeRespecting.comp
    {g : Embedding K L} {f : Embedding H K}
    (hg : g.AuxTypeRespecting) (hf : f.AuxTypeRespecting) :
    (g.comp f).AuxTypeRespecting := by
  constructor
  · intro l a b hla hlb
    exact (hf.one l a b hla hlb).trans
      (hg.one (f l) (f a) (f b)
        (f.strictMono.monotone hla)
        (f.strictMono.monotone hlb))
  · intro l a₀ a₁ b₀ b₁ hla ha hlb hb
    exact (hf.aux l a₀ a₁ b₀ b₁ hla ha hlb hb).trans
      (hg.aux (f l) (f a₀) (f a₁) (f b₀) (f b₁)
        (f.strictMono.monotone hla)
        (f.strictMono ha)
        (f.strictMono.monotone hlb)
        (f.strictMono hb))

/-- If both embeddings fix the first n vertices, then their
genuine induced aux-type-respecting composite fixes them too. -/
theorem comp_fixed_prefix
    (g : Embedding K L) (f : Embedding H K)
    (n : Nat) (hfixF : ∀ i : Nat, i < n → f i = i)
    (hfixG : ∀ i : Nat, i < n → g i = i) :
    ∀ i : Nat, i < n → (g.comp f) i = i := by
  intro i hi
  simp only [comp_apply, hfixF i hi, hfixG i hi]

end Embedding
end Ordered3Graph
end ThreeUniformDiaries
