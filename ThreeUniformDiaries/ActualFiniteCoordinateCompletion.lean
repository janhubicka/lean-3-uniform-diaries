import ThreeUniformDiaries.FiniteActualCandidateRoots
import ThreeUniformDiaries.FiniteStrongCompletion
import ThreeUniformDiaries.FiniteEnumMeetClosure

/-!
# Strong finite vector-picture completion with the manuscript's hypotheses

The preceding genuine finite interface requires induced edge
equivalences and type agreement only for source vertices below m.
It makes NO assumption about artificial source vertices >= m.

We now apply the generic finite strong-completion theorem to the
three concrete prescribed pictures E0, E1 and E2^- on the common
selected level map f. This proves the structural strong-vector-tree
part of manuscript Lemma Aemb under its correct finite type scope.
What remains is constructing the canonical map F_I^S from these
strong sets and verifying the finite coding identity.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- A finite enumeration-prefix picture has a strong completion
without any global induced-embedding hypothesis on the vertex map. -/
theorem exists_finiteEnum_picture_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, f k = k) :
    ∃ r : CoordNode, ∃ S : Set CoordNode,
      (∀ x, finiteEnumCandidate H f n m x → x ∈ S) ∧
      CoordNode.FiniteStrongPicture S f (m - 1) r := by
  let E : Set CoordNode := {x | finiteEnumCandidate H f n m x}
  have hE : CoordNode.MeetClosed E := by
    intro x y hx hy
    exact H.finiteEnumCandidate_meet f hf.strictMono n m x y hx hy
  let r := CoordNode.enum (f 0) (H.truncate (f 0))
  have hrootLevel : CoordNode.level r = f 0 := rfl
  have hroot : ∀ x ∈ E, r ≤ x := by
    intro x hx
    rcases hx with ⟨k, B, hk, rfl⟩ |
      ⟨i, hni, him, rfl⟩
    · have hn : 0 < n := by omega
      have hf0 : f 0 = 0 := hfix 0 hn
      have hbound : f 0 ≤ k := by rw [hf0]; omega
      refine ⟨hbound, ?_⟩
      change CoordNode.enum (f 0) (B.truncate (f 0)) =
        CoordNode.enum (f 0) (H.truncate (f 0))
      rw [hf0]
      have hb : B.truncate 0 = H.truncate 0 := by
        apply EnumNode.ext_triples
        funext a b c
        simp [EnumNode.truncate]
      exact congrArg (CoordNode.enum 0) hb
    · have hcut : f 0 ≤ f i :=
        hf.strictMono.monotone (Nat.zero_le i)
      refine ⟨hcut, ?_⟩
      change CoordNode.enum (f 0)
          ((H.truncate (f i)).truncate (f 0)) =
        CoordNode.enum (f 0) (H.truncate (f 0))
      exact congrArg (CoordNode.enum (f 0))
        (H.truncate_truncate hcut)
  have hlevels :
      ∀ x ∈ E, ∃ i : Nat, i ≤ m - 1 ∧ CoordNode.level x = f i := by
    intro x hx
    rcases hx with ⟨k, B, hk, rfl⟩ |
      ⟨i, hni, him, rfl⟩
    · exact ⟨k, by omega, by
        simpa only [CoordNode.level] using (hfix k hk).symm⟩
    · exact ⟨i, by omega, rfl⟩
  obtain ⟨S, hES, hstrong⟩ :=
    CoordNode.exists_finite_strong_completion E hE
      f hf.strictMono (m - 1) hlevels r hrootLevel hroot
  exact ⟨r, S, fun x hx => hES hx, hstrong⟩

/-- The singleton type coordinate has a finite strong completion
under the genuine finite aux-type-respecting embedding. -/
theorem exists_finiteOne_picture_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, f k = k) :
    ∃ r : CoordNode, ∃ S : Set CoordNode,
      (∀ x, finiteOneCandidate A H f n x → x ∈ S) ∧
      CoordNode.FiniteStrongPicture S f (m - 1) r := by
  let E : Set CoordNode := {x | finiteOneCandidate A H f n x}
  have hE : CoordNode.MeetClosed E := by
    intro x y hx hy
    exact A.finiteOneCandidate_meet_of_finite H f hf n hfix x y hx hy
  obtain ⟨r, hrootLevel, hroot⟩ :=
    A.finiteOne_root_of_finite H f hf n hm hfix
  have hlevels :
      ∀ x ∈ E, ∃ i : Nat, i ≤ m - 1 ∧ CoordNode.level x = f i := by
    intro x hx
    obtain ⟨i, him, hi⟩ :=
      A.oneCandidate_levels_of_map H f n hnm hfix x hx
    exact ⟨i, by omega, hi⟩
  obtain ⟨S, hES, hstrong⟩ :=
    CoordNode.exists_finite_strong_completion E hE
      f hf.strictMono (m - 1) hlevels r hrootLevel
      (fun x hx => hroot x hx)
  exact ⟨r, S, fun x hx => hES hx, hstrong⟩

/-- The auxiliary pair coordinate is also completed directly from
E2^-. The finite strong construction automatically fills its absent
final level, including the one-vertex source case. -/
theorem exists_finiteAux_picture_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, f k = k) :
    ∃ r : CoordNode, ∃ S : Set CoordNode,
      (∀ x, finiteAuxCandidate A H f n x → x ∈ S) ∧
      CoordNode.FiniteStrongPicture S f (m - 1) r := by
  let E : Set CoordNode := {x | finiteAuxCandidate A H f n x}
  have hE : CoordNode.MeetClosed E := by
    intro x y hx hy
    exact A.finiteAuxCandidate_meet_of_finite H f hf n hfix x y hx hy
  obtain ⟨r, hrootLevel, hroot⟩ :=
    A.finiteAux_root_of_finite H f hf n hm hfix
  have hlevels :
      ∀ x ∈ E, ∃ i : Nat, i ≤ m - 1 ∧ CoordNode.level x = f i := by
    intro x hx
    obtain ⟨i, him, hi⟩ :=
      A.auxCandidate_levels_of_map H f n hnm hfix x hx
    exact ⟨i, by omega, hi⟩
  obtain ⟨S, hES, hstrong⟩ :=
    CoordNode.exists_finite_strong_completion E hE
      f hf.strictMono (m - 1) hlevels r hrootLevel
      (fun x hx => hroot x hx)
  exact ⟨r, S, fun x hx => hES hx, hstrong⟩

/-- The three coordinate pictures on EXACTLY the common finite
selected levels f[0,m), proved with only the finite manuscript
embedding conditions, not stronger global zero-extended conditions. -/
theorem exists_threeCoordinate_picture_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, f k = k) :
    ∃ r₀ r₁ r₂ : CoordNode,
      ∃ S₀ S₁ S₂ : Set CoordNode,
      (∀ x, finiteEnumCandidate H f n m x → x ∈ S₀) ∧
      (∀ x, finiteOneCandidate A H f n x → x ∈ S₁) ∧
      (∀ x, finiteAuxCandidate A H f n x → x ∈ S₂) ∧
      CoordNode.FiniteStrongPicture S₀ f (m - 1) r₀ ∧
      CoordNode.FiniteStrongPicture S₁ f (m - 1) r₁ ∧
      CoordNode.FiniteStrongPicture S₂ f (m - 1) r₂ := by
  obtain ⟨r₀, S₀, hS₀, hstr₀⟩ :=
    A.exists_finiteEnum_picture_of_finite H f hf n hnm hm hfix
  obtain ⟨r₁, S₁, hS₁, hstr₁⟩ :=
    A.exists_finiteOne_picture_of_finite H f hf n hnm hm hfix
  obtain ⟨r₂, S₂, hS₂, hstr₂⟩ :=
    A.exists_finiteAux_picture_of_finite H f hf n hnm hm hfix
  exact ⟨r₀, r₁, r₂, S₀, S₁, S₂,
    hS₀, hS₁, hS₂, hstr₀, hstr₁, hstr₂⟩

end EnumNode
end ThreeUniformDiaries
