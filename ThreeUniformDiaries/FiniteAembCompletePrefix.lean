import ThreeUniformDiaries.TypedFiniteCoordinateCompletion

/-!
# Every fixed initial level is literally present in finite Aemb pictures

The manuscript requires S in Str_{n,m}(T), not merely a strong
vector subtree on the selected level set. This means S_j(i)=T_j(i)
for EVERY i<n and for all three type coordinates j<3.

The prescribed candidate sets E0, E1 and E2^- contain the entire
ambient level T_j(i) whenever i<n. Hence every completed finite
strong picture retaining those sets satisfies the fixed-prefix
condition. No new embedding hypotheses or auxiliary choices are used.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- The complete T0 prefix is preserved literally by any picture
containing all the prescribed enumeration candidates. -/
theorem enumCandidate_fullPrefix
    {N : Nat} (H : EnumNode N) (f : Nat → Nat)
    (n m : Nat) {S : Set CoordNode}
    (hinc : ∀ x, finiteEnumCandidate H f n m x → x ∈ S) :
    ∀ (i : Nat) (hi : i < n) (B : EnumNode i),
      CoordNode.enum i B ∈ S := by
  intro i hi B
  exact hinc _ (Or.inl ⟨i, B, hi, rfl⟩)

/-- The complete T1 prefix is retained, not just one chosen branch. -/
theorem oneCandidate_fullPrefix
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat) (n : Nat) {S : Set CoordNode}
    (hinc : ∀ x, finiteOneCandidate A H f n x → x ∈ S) :
    ∀ (i : Nat) (hi : i < n) (B : OneNode i),
      CoordNode.one i B ∈ S := by
  intro i hi B
  exact hinc _ (Or.inl ⟨i, B, hi, rfl⟩)

/-- The complete T2 prefix is retained, including all auxiliary
nodes when no selected pair type occurs yet. -/
theorem auxCandidate_fullPrefix
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat) (n : Nat) {S : Set CoordNode}
    (hinc : ∀ x, finiteAuxCandidate A H f n x → x ∈ S) :
    ∀ (i : Nat) (hi : i < n) (B : AuxNode i),
      CoordNode.aux i B ∈ S := by
  intro i hi B
  exact hinc _ (Or.inl ⟨i, B, hi, rfl⟩)

/-- The three fixed-prefix conditions follow simultaneously from
the actual finite candidate containments; these are precisely
the additional first-n-level requirements of Str_{n,m}. -/
theorem threeCandidate_fullPrefix
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat) (n : Nat)
    {S₀ S₁ S₂ : Set CoordNode}
    (hinc₀ : ∀ x, finiteEnumCandidate H f n m x → x ∈ S₀)
    (hinc₁ : ∀ x, finiteOneCandidate A H f n x → x ∈ S₁)
    (hinc₂ : ∀ x, finiteAuxCandidate A H f n x → x ∈ S₂) :
    (∀ (i : Nat) (hi : i < n) (B : EnumNode i),
      CoordNode.enum i B ∈ S₀) ∧
    (∀ (i : Nat) (hi : i < n) (B : OneNode i),
      CoordNode.one i B ∈ S₁) ∧
    (∀ (i : Nat) (hi : i < n) (B : AuxNode i),
      CoordNode.aux i B ∈ S₂) := by
  exact ⟨enumCandidate_fullPrefix H f n m hinc₀,
    oneCandidate_fullPrefix A H f n hinc₁,
    auxCandidate_fullPrefix A H f n hinc₂⟩

end EnumNode
end ThreeUniformDiaries
