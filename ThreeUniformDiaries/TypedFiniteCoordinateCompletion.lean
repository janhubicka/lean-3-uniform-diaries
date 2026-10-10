import ThreeUniformDiaries.FiniteStrongRootLevel
import ThreeUniformDiaries.ActualFiniteCoordinateCompletion

/-!
# Typed finite strong pictures under the genuine finite Aemb hypotheses

The original finite-coordinate completion theorem returns three roots
of the common untyped CoordNode forest. Except for the empty auxiliary
carrier at m=1,n=0, each candidate picture contains a node on the first
selected level f(0). Since every finite strong picture has its root on
that level, the candidate identifies its coordinate type literally.

In the exceptional one-vertex, empty-prefix case, E2^- is empty.
Construct an auxiliary-coordinate strong picture directly with an
auxiliary root, rather than extracting one from an empty candidate
picture. No change to the manuscript's finite embedding hypotheses.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem exists_typed_finiteEnum_picture_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, f k = k) :
    ∃ (r : EnumNode (f 0)) (S : Set CoordNode),
      (∀ x, finiteEnumCandidate H f n m x → x ∈ S) ∧
      CoordNode.FiniteStrongPicture S f (m - 1)
        (.enum (f 0) r) := by
  obtain ⟨r, S, hinc, hstrong⟩ :=
    A.exists_finiteEnum_picture_of_finite H f hf n hnm hm hfix
  let q : EnumNode (f 0) := H.truncate (f 0)
  have hq : CoordNode.enum (f 0) q ∈ S := by
    apply hinc
    by_cases hn : n = 0
    · exact Or.inr ⟨0, by omega, hm, rfl⟩
    · have h0 : f 0 = 0 := hfix 0 (by omega)
      exact Or.inl ⟨f 0, q, by rw [h0]; omega, rfl⟩
  have hr : r = CoordNode.enum (f 0) q :=
    CoordNode.finiteStrongPicture_root_eq_of_first_level
      hstrong hf.strictMono _ hq rfl
  rw [hr] at hstrong
  exact ⟨q, S, hinc, hstrong⟩

theorem exists_typed_finiteOne_picture_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, f k = k) :
    ∃ (r : OneNode (f 0)) (S : Set CoordNode),
      (∀ x, finiteOneCandidate A H f n x → x ∈ S) ∧
      CoordNode.FiniteStrongPicture S f (m - 1)
        (.one (f 0) r) := by
  obtain ⟨r, S, hinc, hstrong⟩ :=
    A.exists_finiteOne_picture_of_finite H f hf n hnm hm hfix
  let q : OneNode (f 0) := H.oneType (f 0) (f 0)
  have hq : CoordNode.one (f 0) q ∈ S := by
    apply hinc
    by_cases hn : n = 0
    · exact Or.inr ⟨0, 0, by omega, Nat.le_refl 0, hm, rfl⟩
    · have h0 : f 0 = 0 := hfix 0 (by omega)
      exact Or.inl ⟨f 0, q, by rw [h0]; omega, rfl⟩
  have hr : r = CoordNode.one (f 0) q :=
    CoordNode.finiteStrongPicture_root_eq_of_first_level
      hstrong hf.strictMono _ hq rfl
  rw [hr] at hstrong
  exact ⟨q, S, hinc, hstrong⟩

theorem exists_typed_finiteAux_picture_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, f k = k) :
    ∃ (r : AuxNode (f 0)) (S : Set CoordNode),
      (∀ x, finiteAuxCandidate A H f n x → x ∈ S) ∧
      CoordNode.FiniteStrongPicture S f (m - 1)
        (.aux (f 0) r) := by
  by_cases hexception : n = 0 ∧ m = 1
  · obtain ⟨hn, hm1⟩ := hexception
    subst n
    subst m
    let E : Set CoordNode := ∅
    let root : CoordNode :=
      .aux (f 0) (AuxNode.zero (f 0))
    have hclosed : CoordNode.MeetClosed E := by
      intro x y hx hy
      exact False.elim hx
    have hlevels :
        ∀ x ∈ E, ∃ i : Nat,
          i ≤ 1 - 1 ∧ CoordNode.level x = f i := by
      intro x hx
      exact False.elim hx
    have hrootlevel : CoordNode.level root = f 0 := rfl
    have hbelow : ∀ x ∈ E, root ≤ x := by
      intro x hx
      exact False.elim hx
    obtain ⟨S, _, hstrong⟩ :=
      CoordNode.exists_finite_strong_completion
        E hclosed f hf.strictMono (1 - 1)
          hlevels root hrootlevel hbelow
    refine ⟨AuxNode.zero (f 0), S, ?_, hstrong⟩
    intro x hx
    rcases hx with ⟨k, B, hk, heq⟩ |
        ⟨i, u₀, u₁, hni, hiu, hu, hum, heq⟩
    · omega
    · omega
  · obtain ⟨r, S, hinc, hstrong⟩ :=
      A.exists_finiteAux_picture_of_finite H f hf n hnm hm hfix
    obtain ⟨q, hq⟩ :
        ∃ (q : AuxNode (f 0)),
          CoordNode.aux (f 0) q ∈ S := by
      by_cases hn : n = 0
      · have hm2 : 1 < m := by omega
        refine ⟨H.auxType (f 0) (f 0) (f 1), ?_⟩
        apply hinc
        exact Or.inr ⟨0, 0, 1, by omega,
          Nat.le_refl 0, Nat.zero_lt_one, hm2, rfl⟩
      · have h0 : f 0 = 0 := hfix 0 (by omega)
        refine ⟨AuxNode.zero (f 0), ?_⟩
        apply hinc
        exact Or.inl ⟨f 0, AuxNode.zero (f 0),
          by rw [h0]; omega, rfl⟩
    have hr : r = CoordNode.aux (f 0) q :=
      CoordNode.finiteStrongPicture_root_eq_of_first_level
        hstrong hf.strictMono _ hq rfl
    rw [hr] at hstrong
    exact ⟨q, S, hinc, hstrong⟩

/-- Precisely synchronized typed E0/E1/E2 strong pictures,
without any extra global or artificial-vertex hypotheses. -/
theorem exists_typed_threeCoordinate_picture_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, f k = k) :
    ∃ (r₀ : EnumNode (f 0))
      (r₁ : OneNode (f 0)) (r₂ : AuxNode (f 0)),
      ∃ S₀ S₁ S₂ : Set CoordNode,
        (∀ x, finiteEnumCandidate H f n m x → x ∈ S₀) ∧
        (∀ x, finiteOneCandidate A H f n x → x ∈ S₁) ∧
        (∀ x, finiteAuxCandidate A H f n x → x ∈ S₂) ∧
        CoordNode.FiniteStrongPicture S₀ f (m - 1)
          (.enum (f 0) r₀) ∧
        CoordNode.FiniteStrongPicture S₁ f (m - 1)
          (.one (f 0) r₁) ∧
        CoordNode.FiniteStrongPicture S₂ f (m - 1)
          (.aux (f 0) r₂) := by
  obtain ⟨r₀, S₀, hinc₀, hstr₀⟩ :=
    A.exists_typed_finiteEnum_picture_of_finite
      H f hf n hnm hm hfix
  obtain ⟨r₁, S₁, hinc₁, hstr₁⟩ :=
    A.exists_typed_finiteOne_picture_of_finite
      H f hf n hnm hm hfix
  obtain ⟨r₂, S₂, hinc₂, hstr₂⟩ :=
    A.exists_typed_finiteAux_picture_of_finite
      H f hf n hnm hm hfix
  exact ⟨r₀, r₁, r₂, S₀, S₁, S₂,
    hinc₀, hinc₁, hinc₂, hstr₀, hstr₁, hstr₂⟩

end EnumNode
end ThreeUniformDiaries
