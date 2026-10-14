import ThreeUniformDiaries.DiaryFinitePointedEnumNode
import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Finite auxiliary-bit and orientation colours of pointed leaf pairs

The pair part of the lower-bound type-stabilisation lemma colours
each actual finite embedding of a pointed pair envelope by:
* its auxiliary edge bits below the fixed target cut N, and
* the lexicographic orientation of its two distinguished leaves.

This colour is genuinely finite, even when the target is an arbitrary
countable enumerated hypergraph and the ambient embedding skips
vertices. Equality of colours is EXACTLY equality of the auxiliary
pair types over N together with the orientation bit. No premature
assumption of one-type stabilisation enters this calculation.
-/

namespace ThreeUniformDiaries
namespace DiaryLowerBoundColors

open Ordered3Graph
open DiaryLeafPriority

/-- The finite colour used for two distinguished leaves at a target
cut N. The function of Fin N records all auxiliary pair bits. -/
noncomputable def pairColour
    (K : Ordered3Graph Nat) (N a b : Nat) :
    (Fin N → Bool) × Bool := by
  classical
  exact (fun z => decide (K.edge z.val a b),
    decide (LexEarlier K a b))

/-- The pair colour decoder is exact: its first component is the
auxiliary 2-type below N, and its second component is the target
lexicographic orientation. -/
theorem pairColour_eq_iff
    (K : Ordered3Graph Nat) (N a b c d : Nat) :
    pairColour K N a b = pairColour K N c d ↔
      K.SameAuxTypeBelow N a b c d ∧
        (LexEarlier K a b ↔ LexEarlier K c d) := by
  classical
  constructor
  · intro h
    have hbits := congrArg Prod.fst h
    have horientation := congrArg Prod.snd h
    constructor
    · intro z hz
      have hbit := congrFun hbits (⟨z, hz⟩ : Fin N)
      change decide (K.edge z a b) =
        decide (K.edge z c d) at hbit
      by_cases ha : K.edge z a b
      · by_cases hb : K.edge z c d
        · exact iff_of_true ha hb
        · simp [ha, hb] at hbit
      · by_cases hb : K.edge z c d
        · simp [ha, hb] at hbit
        · exact iff_of_false ha hb
    · change decide (LexEarlier K a b) =
        decide (LexEarlier K c d) at horientation
      by_cases ha : LexEarlier K a b
      · by_cases hb : LexEarlier K c d
        · exact iff_of_true ha hb
        · simp [ha, hb] at horientation
      · by_cases hb : LexEarlier K c d
        · simp [ha, hb] at horientation
        · exact iff_of_false ha hb
  · rintro ⟨haux, horient⟩
    apply Prod.ext
    · funext z
      change decide (K.edge z.val a b) =
        decide (K.edge z.val c d)
      have htype := haux (a := z.val) z.isLt
      by_cases ha : K.edge z.val a b
      · have hb : K.edge z.val c d := htype.mp ha
        simp [ha, hb]
      · have hb : ¬ K.edge z.val c d := by
          intro h
          exact ha (htype.mpr h)
        simp [ha, hb]
    · change decide (LexEarlier K a b) =
        decide (LexEarlier K c d)
      by_cases ha : LexEarlier K a b
      · have hb : LexEarlier K c d := horient.mp ha
        simp [ha, hb]
      · have hb : ¬ LexEarlier K c d := by
          intro h
          exact ha (horient.mpr h)
        simp [ha, hb]

end DiaryLowerBoundColors

namespace Ordered3Graph
namespace FinitePointedEnvelope

variable {G : Ordered3Graph Nat} {j a b : Nat}

/-- Source position of the first distinguished leaf. -/
def firstLeafIndex (E : FinitePointedEnvelope G j a b) :
    Fin E.size :=
  ⟨E.size - 2, by have hs := E.size_lower; omega⟩

/-- Source position of the second distinguished leaf. -/
def secondLeafIndex (E : FinitePointedEnvelope G j a b) :
    Fin E.size :=
  ⟨E.size - 1, by have hs := E.size_lower; omega⟩

/-- Colour a genuine finite code of the envelope using ONLY the
images of its two final vertices. F maps the ambient source
vertices into the target K; it need not respect types for the
colour to be defined. -/
noncomputable def pairColourOfCode
    (E : FinitePointedEnvelope G j a b)
    (K : Ordered3Graph Nat) (F : Nat → Nat) (N : Nat)
    (e : FiniteAuxEmbeddingImage E.finiteEnum.toOrdered3Graph G E.size) :
    (Fin N → Bool) × Bool :=
  DiaryLowerBoundColors.pairColour K N
    (F (e.image E.firstLeafIndex))
    (F (e.image E.secondLeafIndex))

/-- Equality of finite-code colours is exactly agreement of
auxiliary pair types and lexicographic orientation below N. -/
theorem pairColourOfCode_eq_iff
    (E : FinitePointedEnvelope G j a b)
    (K : Ordered3Graph Nat) (F : Nat → Nat) (N : Nat)
    (e₀ e₁ : FiniteAuxEmbeddingImage
      E.finiteEnum.toOrdered3Graph G E.size) :
    E.pairColourOfCode K F N e₀ =
      E.pairColourOfCode K F N e₁ ↔
      K.SameAuxTypeBelow N
        (F (e₀.image E.firstLeafIndex))
        (F (e₀.image E.secondLeafIndex))
        (F (e₁.image E.firstLeafIndex))
        (F (e₁.image E.secondLeafIndex)) ∧
      (DiaryLeafPriority.LexEarlier K
          (F (e₀.image E.firstLeafIndex))
          (F (e₀.image E.secondLeafIndex)) ↔
       DiaryLeafPriority.LexEarlier K
          (F (e₁.image E.firstLeafIndex))
          (F (e₁.image E.secondLeafIndex))) := by
  exact DiaryLowerBoundColors.pairColour_eq_iff K N
    (F (e₀.image E.firstLeafIndex))
    (F (e₀.image E.secondLeafIndex))
    (F (e₁.image E.firstLeafIndex))
    (F (e₁.image E.secondLeafIndex))

/-- On the canonical finite envelope inclusion the colour reduces
to the genuine target images a,b, with no reference to tail data. -/
theorem pairColourOfCode_canonical
    (E : FinitePointedEnvelope G j a b)
    (K : Ordered3Graph Nat) (F : Nat → Nat) (N : Nat) :
    E.pairColourOfCode K F N E.finiteATRCode =
      DiaryLowerBoundColors.pairColour K N (F a) (F b) := by
  have hfirst : E.finiteATRCode.image E.firstLeafIndex = a := by
    simpa only [firstLeafIndex] using E.finiteATRCode_final_endpoints.1
  have hsecond : E.finiteATRCode.image E.secondLeafIndex = b := by
    simpa only [secondLeafIndex] using E.finiteATRCode_final_endpoints.2
  simp only [pairColourOfCode, hfirst, hsecond]

end FinitePointedEnvelope
end Ordered3Graph
end ThreeUniformDiaries
