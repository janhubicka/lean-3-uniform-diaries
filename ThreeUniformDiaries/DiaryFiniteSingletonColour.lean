import ThreeUniformDiaries.DiaryFiniteSingletonATR

/-!
# The exact finite singleton-type colour for lower-bound stabilisation

The singleton stage of the diary lower-bound proof colours each
prefix-fixing copy of a singleton envelope by the image vertex's
one-type over a fixed finite cut N of the *arbitrary target*.

To make the colour a finite genuine ATR colouring, record the edge
bits for all ordered index-pairs in Fin N. Entries for non-increasing
pairs are set to false, so equality of colours is precisely
SameOneTypeBelow N and does not require non-edge assumptions about
non-increasing triples of arbitrary target graphs.

The colouring depends only on the image of the one actual terminal
vertex of a finite singleton envelope, not an infinite extension.
-/

namespace ThreeUniformDiaries
namespace DiaryLowerBoundColors

open Ordered3Graph

/-- Finite Boolean mask for a singleton's complete 1-type below N.
Tests outside the increasing-pair domain are identically false. -/
noncomputable def singletonColour
    (K : Ordered3Graph Nat) (N v : Nat) :
    Fin N → Fin N → Bool := by
  classical
  exact fun x y =>
    if x.val < y.val then decide (K.edge x.val y.val v)
    else false

/-- Two finite singleton colours coincide exactly when their
vertices have the same singleton type below the target cut. -/
theorem singletonColour_eq_iff
    (K : Ordered3Graph Nat) (N v w : Nat) :
    singletonColour K N v = singletonColour K N w ↔
      K.SameOneTypeBelow N v w := by
  classical
  constructor
  · intro h x y hxy hy
    have hbit := congrFun (congrFun h (⟨x, by omega⟩ : Fin N))
      (⟨y, hy⟩ : Fin N)
    have hdec : decide (K.edge x y v) =
        decide (K.edge x y w) := by
      simpa [singletonColour, hxy] using hbit
    by_cases hv : K.edge x y v <;> by_cases hw : K.edge x y w
    all_goals simp_all [hv, hw]
  · intro h
    funext x y
    by_cases hxy : x.val < y.val
    · have heq := h hxy y.isLt
      change (if x.val < y.val then decide (K.edge x.val y.val v)
        else false) =
        (if x.val < y.val then decide (K.edge x.val y.val w)
        else false)
      simp only [if_pos hxy]
      by_cases hv : K.edge x.val y.val v <;>
        by_cases hw : K.edge x.val y.val w
      all_goals simp_all [hv, hw]
    · change (if x.val < y.val then decide (K.edge x.val y.val v)
        else false) =
        (if x.val < y.val then decide (K.edge x.val y.val w)
        else false)
      simp [hxy]

end DiaryLowerBoundColors

namespace Ordered3Graph
namespace FiniteSingletonEnvelope

variable {G : Ordered3Graph Nat} {n a : Nat}

/-- The unique exterior actual vertex of a singleton envelope. -/
def terminalIndex (E : FiniteSingletonEnvelope G n a) :
    Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

/-- The source of the target 1-type mask is a genuine finite ATR
embedding of the singleton envelope. No continuation values enter. -/
noncomputable def singletonColourOfCode
    (E : FiniteSingletonEnvelope G n a)
    (K : Ordered3Graph Nat) (F : Nat → Nat) (N : Nat)
    (e : FiniteAuxEmbeddingImage E.finiteEnum.toOrdered3Graph
       G (n + 1)) :
    Fin N → Fin N → Bool :=
  DiaryLowerBoundColors.singletonColour K N
    (F (e.image E.terminalIndex))

/-- Equal finite-code colours are exactly equal target singleton
types of their actual final vertices over the specified cut. -/
theorem singletonColourOfCode_eq_iff
    (E : FiniteSingletonEnvelope G n a)
    (K : Ordered3Graph Nat) (F : Nat → Nat) (N : Nat)
    (e₀ e₁ : FiniteAuxEmbeddingImage
      E.finiteEnum.toOrdered3Graph G (n+1)) :
    E.singletonColourOfCode K F N e₀ =
      E.singletonColourOfCode K F N e₁ ↔
      K.SameOneTypeBelow N
        (F (e₀.image E.terminalIndex))
        (F (e₁.image E.terminalIndex)) := by
  exact DiaryLowerBoundColors.singletonColour_eq_iff K N
    (F (e₀.image E.terminalIndex))
    (F (e₁.image E.terminalIndex))

/-- The canonical code's colour is the actual target type of a. -/
theorem singletonColourOfCode_canonical
    (E : FiniteSingletonEnvelope G n a)
    (K : Ordered3Graph Nat) (F : Nat → Nat) (N : Nat) :
    E.singletonColourOfCode K F N E.finiteATRCode =
      DiaryLowerBoundColors.singletonColour K N (F a) := by
  have hlast : E.finiteATRCode.image E.terminalIndex = a := by
    simpa only [terminalIndex] using E.finiteATRCode_last
  simp only [singletonColourOfCode, hlast]

end FiniteSingletonEnvelope
end Ordered3Graph
end ThreeUniformDiaries
