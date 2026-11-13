import ThreeUniformDiaries.DiaryRelativeFamilyExactOldImageCompression
import ThreeUniformDiaries.DiaryFiniteFamilyStrongAbsorbers
import ThreeUniformDiaries.DiaryFiniteFlipAbsorptionUpwardClosure

/-!
# Track B: a relative finite strong absorber follows from ONE common ambient

The verified finite strong-absorption theorem supplies one finite
universal target U_t for ALL source diaries of each prescribed
finite source frame t, and its absorption persists along any
bounded protected target all-meet embedding.

The remaining issue is making that universal absorber occur INSIDE
the same countable full RoleDiary G as an already prescribed
finite old source-copy map f:B->G, with the entire actual old
image bounded below p. We take this **common ambient input** as
an EXPLICIT hypothesis here.

The new finite-family literal-extraction theorem then compresses
the particular old map f and the one universal target U_t into
ONE genuine finite full C. The old map's numerical ranks remain
exactly f(u); C has a terminal leaf beyond the whole old image.
By verified upward closure, C absorbs EVERY t-frame finite diary
in EACH of its genuine finite target flips.

This cleanly isolates the unresolved positive construction to a
countable relative JEP/embedding problem (plus recursive
admissibility), rather than finite compression or flip absorption
of the finished target. No relative ambient existence is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A common full countable diary containing a PARTICULAR bounded
old finite copy and one bounded all-meet copy of a universal
t-frame flip absorber yields ONE relative finite strong absorber
successor, keeping the old copy's exact numerical coordinates
and a free true terminal leaf.

The common countable-ambient embedding of the universal absorber
is an explicit premise. Merely knowing abstract finite JEP does
not produce it while fixing the old numerical image f. -/
theorem exists_relative_finite_strong_absorber_of_common_ambient
    {B G : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}
    (DB : FiniteRoleDiaryBlock B n) (hn : 4 ≤ n)
    (DG : RoleDiary G)
    (EB : FiniteMeetEmbedding B G n f)
    (p : Nat)
    (hOldBound : ∀ u : Nat, u < n → f u < p)
    (t : Nat)
    (hUniversalAmbient :
      ∃ (U : Ordered3Graph Nat) (j : Nat),
        FiniteRoleDiaryBlock U j ∧
        (∀ A : Ordered3Graph Nat, FiniteRoleDiaryBlock A t →
          AbsorbsEveryTargetFlipInside A U t j) ∧
        (∃ e : Nat → Nat, FiniteMeetEmbedding U G j e)) :
    ∃ (C : Ordered3Graph Nat) (k : Nat) (g : Nat → Nat),
      FiniteRoleDiaryBlock C k ∧
      p < k ∧
      FiniteBoundedMeetEmbedding B C n k g ∧
      (∀ u : Nat, u < n → g u = f u) ∧
      (∀ A : Ordered3Graph Nat, FiniteRoleDiaryBlock A t →
        AbsorbsEveryTargetFlipInside A C t k) ∧
      (∀ a b c : Nat, a < b → b < c → c < p →
        (C.edge a b c ↔ G.edge a b c)) ∧
      IsLeaf C (k-1) ∧
      (∀ u : Nat, u < n → g u < k-1) := by
  classical
  obtain ⟨U,j,DU,hEvery,e,EU⟩ := hUniversalAmbient
  let D : FiniteDiaryInput := ⟨U,j,DU⟩
  have hCopies : ∀ X : FiniteDiaryInput, X ∈ [D] →
      ∃ h : Nat → Nat, FiniteMeetEmbedding X.graph G X.bound h := by
    intro X hX
    have heq : X = D := by simpa only [List.mem_singleton] using hX
    subst X
    exact ⟨e,EU⟩
  obtain ⟨C,k,g,DC,hPk,Eg,hEq,hFamily,hEdges,hLast,hFree⟩ :=
    exists_finiteDiary_preserving_one_exact_image_and_family
      DB hn DG EB p hOldBound [D] hCopies
  obtain ⟨h,Eh⟩ := hFamily D (by simp)
  have hAbs : ∀ A : Ordered3Graph Nat,
      FiniteRoleDiaryBlock A t →
      AbsorbsEveryTargetFlipInside A C t k := by
    intro A DA
    exact absorbsEveryTargetFlipInside_of_target_embedding
      DU (hEvery A DA) Eh
  exact ⟨C,k,g,DC,hPk,Eg,hEq,hAbs,hEdges,hLast,hFree⟩

end DiaryLeafPriority
end ThreeUniformDiaries
