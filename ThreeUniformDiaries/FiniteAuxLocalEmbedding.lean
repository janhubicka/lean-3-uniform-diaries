import ThreeUniformDiaries.FiniteAuxEmbeddingImage

/-!
# Equivalence with genuinely bounded finite aux-embedding conditions

The finite colouring must include every m-vertex aux-type-respecting
embedding, not just a specially extendable subclass. We show that
strictly increasing images on Fin m, preserving and reflecting the
edge, singleton and auxiliary tests for genuine source indices below
m, ALWAYS extend to a strictly increasing Nat map.

The extension is unconstrained outside the original m vertices and
does not impose artificial edge or type tests involving that tail.
Thus the Prop-based finite image representation used for colouring
is exactly the intended purely finite local class.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Entirely finite aux embedding data. All source indices are
elements of Fin m; no arbitrary out-of-range vertices can be tested. -/
structure FiniteAuxLocalEmbedding
    (H K : Ordered3Graph Nat) (m : Nat) where
  image : Fin m → Nat
  strictMono : StrictMono image
  edge_iff : ∀ a b c : Fin m, a < b → b < c →
    (H.edge a.val b.val c.val ↔
      K.edge (image a) (image b) (image c))
  one_iff : ∀ l u v : Fin m, l ≤ u → l ≤ v →
    (H.SameOneTypeBelow l.val u.val v.val ↔
      K.SameOneTypeBelow (image l) (image u) (image v))
  aux_iff : ∀ l a b c d : Fin m,
    l ≤ a → a < b → l ≤ c → c < d →
    (H.SameAuxTypeBelow l.val a.val b.val c.val d.val ↔
      K.SameAuxTypeBelow (image l)
        (image a) (image b) (image c) (image d))

namespace FiniteAuxLocalEmbedding

variable {H K : Ordered3Graph Nat} {m : Nat}

/-- Extend only the finite ordered vertex images, using consecutive
values above the last image. The case m=0 is the identity extension. -/
noncomputable def extend (e : FiniteAuxLocalEmbedding H K m)
    (i : Nat) : Nat :=
  if hi : i < m then e.image ⟨i, hi⟩
  else if hm : 0 < m then
    e.image ⟨m - 1, by omega⟩ + (i - (m - 1))
  else i

@[simp] theorem extend_inside (e : FiniteAuxLocalEmbedding H K m)
    (i : Nat) (hi : i < m) :
    e.extend i = e.image ⟨i, hi⟩ := by
  simp [extend, hi]

theorem extend_outside (e : FiniteAuxLocalEmbedding H K m)
    (i : Nat) (hi : m ≤ i) (hm : 0 < m) :
    e.extend i =
      e.image ⟨m - 1, by omega⟩ + (i - (m - 1)) := by
  simp [extend, Nat.not_lt.mpr hi, hm]

theorem extend_zero (e : FiniteAuxLocalEmbedding H K m)
    (hm : m = 0) (i : Nat) :
    e.extend i = i := by
  subst m
  simp [extend]

/-- Every strictly increasing finite image map has a strictly
increasing global extension. Nothing about hyperedges beyond the
finite source is used or inferred. -/
theorem extend_strictMono (e : FiniteAuxLocalEmbedding H K m) :
    StrictMono e.extend := by
  intro i j hij
  by_cases hi : i < m
  · by_cases hj : j < m
    · rw [e.extend_inside i hi, e.extend_inside j hj]
      apply e.strictMono
      change i < j
      exact hij
    · have hm : 0 < m := by omega
      rw [e.extend_inside i hi,
        e.extend_outside j (by omega) hm]
      have hle :
          e.image ⟨i, hi⟩ ≤ e.image ⟨m - 1, by omega⟩ := by
        apply e.strictMono.monotone
        change i ≤ m - 1
        omega
      omega
  · have hj : m ≤ j := by omega
    have hi' : m ≤ i := Nat.le_of_not_gt hi
    by_cases hm : 0 < m
    · rw [e.extend_outside i hi' hm, e.extend_outside j hj hm]
      omega
    · have hzero : m = 0 := by omega
      rw [e.extend_zero hzero i, e.extend_zero hzero j]
      exact hij

/-- The finite local constraints extend to precisely the
FiniteAuxEmbedding hypothesis already used by the manuscript's
finite Aemb coding. No global aux-type preservation is imposed. -/
theorem toFiniteAuxEmbedding (e : FiniteAuxLocalEmbedding H K m) :
    FiniteAuxEmbedding H K e.extend m := by
  refine ⟨e.extend_strictMono, ?_, ?_, ?_⟩
  · intro a b c hab hbc hc
    have ha : a < m := by omega
    have hb : b < m := by omega
    have h := e.edge_iff ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
      (by exact hab) (by exact hbc)
    simpa only [e.extend_inside a ha,
      e.extend_inside b hb, e.extend_inside c hc] using h
  · intro l u v hlu hlv hu hv
    have hl : l < m := by omega
    have h := e.one_iff ⟨l, hl⟩ ⟨u, hu⟩ ⟨v, hv⟩
      (by exact hlu) (by exact hlv)
    simpa only [e.extend_inside l hl,
      e.extend_inside u hu, e.extend_inside v hv] using h
  · intro l a b c d hla hab hlc hcd hb hd
    have hl : l < m := by omega
    have ha : a < m := by omega
    have hc : c < m := by omega
    have h := e.aux_iff ⟨l, hl⟩ ⟨a, ha⟩ ⟨b, hb⟩
      ⟨c, hc⟩ ⟨d, hd⟩
      (by exact hla) (by exact hab) (by exact hlc) (by exact hcd)
    simpa only [e.extend_inside l hl,
      e.extend_inside a ha, e.extend_inside b hb,
      e.extend_inside c hc, e.extend_inside d hd] using h

/-- Every purely finite local embedding belongs to the genuine
finite-image colouring domain. -/
def toFiniteImage (e : FiniteAuxLocalEmbedding H K m) :
    FiniteAuxEmbeddingImage H K m where
  image := e.image
  admissible := ⟨e.extend, e.toFiniteAuxEmbedding, by
    intro i
    exact (e.extend_inside i.val i.isLt).symm⟩

end FiniteAuxLocalEmbedding

namespace FiniteAuxEmbeddingImage

variable {H K : Ordered3Graph Nat} {m : Nat}

/-- Recover all and only the bounded local edge and type tests of a
finite image code. The global extension is used only as a witness,
not as part of the code's equality or colouring. -/
noncomputable def toLocal (e : FiniteAuxEmbeddingImage H K m) :
    FiniteAuxLocalEmbedding H K m := by
  classical
  obtain ⟨f, hf, he⟩ := e.admissible
  refine {
    image := e.image
    strictMono := ?_
    edge_iff := ?_
    one_iff := ?_
    aux_iff := ?_
  }
  · intro i j hij
    rw [he i, he j]
    exact hf.strictMono hij
  · intro a b c hab hbc
    have h := hf.edge_iff a.val b.val c.val
      (by exact hab) (by exact hbc) c.isLt
    simpa only [he a, he b, he c] using h
  · intro l u v hlu hlv
    have h := hf.one l.val u.val v.val
      (by exact hlu) (by exact hlv) u.isLt v.isLt
    simpa only [he l, he u, he v] using h
  · intro l a b c d hla hab hlc hcd
    have h := hf.aux l.val a.val b.val c.val d.val
      (by exact hla) (by exact hab) (by exact hlc) (by exact hcd)
      b.isLt d.isLt
    simpa only [he l, he a, he b, he c, he d] using h

/-- No genuine finite embedding is lost by the finite-image
representation: recovering the local map and converting back is
literally the same point of the finite colouring domain. -/
theorem toLocal_toFiniteImage (e : FiniteAuxEmbeddingImage H K m) :
    e.toLocal.toFiniteImage = e := by
  ext i
  rfl

end FiniteAuxEmbeddingImage
end Ordered3Graph
end ThreeUniformDiaries
