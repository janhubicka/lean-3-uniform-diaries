import ThreeUniformDiaries.DiaryStableGenericPairPatternColour

/-!
# Track C: exponentially branching cofinal complete singleton colours

English-first mathematical proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #293

For any FINITE collection S of pair tests u<v<B ACTUALLY represented
in an original induced generic true-leaf range F[G], every Boolean
assignment to S extends to a cofinally attained COMPLETE mixed singleton
colour. These colours can be selected simultaneously, with literal
restriction to S giving a left inverse; hence there are at least 2^|S|
distinct cofinally inhabited finite colours.

The result is strictly leaf-only: it supplies no generic subcopy in any
one colour, prescribed marker/E2/E3/S1/S2 generators, or persistence
through future diary horizons.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Extend a finite prescribed Boolean pattern on an explicitly
represented subset of target-ordered pairs below B to a TOTAL Boolean
pattern on arbitrary target pairs. Entries outside S are false. -/
def extendSupportedGenericPairPattern
    (B : Nat) (S : Finset (Fin B × Fin B))
    (q : {p : Fin B × Fin B // p ∈ S} → Bool)
    (x y : Nat) : Bool :=
  if hx : x < B then
    if hy : y < B then
      if hp : ((⟨x, hx⟩ : Fin B), (⟨y, hy⟩ : Fin B)) ∈ S then
        q ⟨((⟨x, hx⟩ : Fin B), (⟨y, hy⟩ : Fin B)), hp⟩
      else false
    else false
  else false

/-- On a selected finite pair, total pattern extension retains exactly
the original prescribed Boolean bit. -/
theorem extendSupportedGenericPairPattern_at
    {B : Nat} {S : Finset (Fin B × Fin B)}
    (q : {p : Fin B × Fin B // p ∈ S} → Bool)
    (p : {p : Fin B × Fin B // p ∈ S}) :
    extendSupportedGenericPairPattern B S q p.val.1.val p.val.2.val =
      q p := by
  rcases p with ⟨⟨u, v⟩, hp⟩
  simp [extendSupportedGenericPairPattern, u.isLt, v.isLt, hp]

/-- Restrict a COMPLETE mixed singleton colour to finitely many
specified target pair bits. -/
def genericPairColourOn
    (B : Nat) (S : Finset (Fin B × Fin B))
    (c : Fin B → Fin B → Bool) :
    {p : Fin B × Fin B // p ∈ S} → Bool :=
  fun p => c p.val.1 p.val.2

/-- Exponential finite branching of the cofinal full-colour palette.

S contains strictly target-ordered pairs u<v<B, whose endpoints
are BOTH actually images of vertices of the ORIGINAL generic copy F[G].
For every Boolean assignment q to S, one COMPLETE mixed singleton colour
is cofinally realized in F[G], both in source indices and target values,
with all selected bits equal to q.

All chosen colours are different for different q, witnessed by a
literal left inverse (restriction to S). In particular the set of
cofinally attained complete B-colours has at least 2^S.card elements.

There is NO assertion that the selected colour classes are themselves
generic, or that they preserve any prescribed relative S1/S2/E2/E3
generator table or survive all future source horizons. -/
theorem exists_injective_cofinal_generic_pair_colour_section
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hLeaves : ∀ t : Nat, IsLeaf K (F t))
    (B : Nat) (S : Finset (Fin B × Fin B))
    (hRepresented : ∀ p : Fin B × Fin B, p ∈ S →
      p.1 < p.2 ∧
        ∃ i j : Nat, F i = p.1.val ∧ F j = p.2.val) :
    ∃ select :
        ({p : Fin B × Fin B // p ∈ S} → Bool) →
          (Fin B → Fin B → Bool),
      Function.Injective select ∧
      (∀ q : {p : Fin B × Fin B // p ∈ S} → Bool,
        HasCofinalGenericPairPatternColour G K F B
          (extendSupportedGenericPairPattern B S q) (select q)) ∧
      (∀ q : {p : Fin B × Fin B // p ∈ S} → Bool,
        genericPairColourOn B S (select q) = q) := by
  classical
  let Pattern := ({p : Fin B × Fin B // p ∈ S} → Bool)
  have hChoose (q : Pattern) :
      ∃ c : Fin B → Fin B → Bool,
        HasCofinalGenericPairPatternColour G K F B
          (extendSupportedGenericPairPattern B S q) c :=
    exists_cofinal_generic_pair_pattern_full_colour
      G K F hLeaves B (extendSupportedGenericPairPattern B S q)
  let select (q : Pattern) : Fin B → Fin B → Bool :=
    Classical.choose (hChoose q)
  have hCofinal (q : Pattern) :
      HasCofinalGenericPairPatternColour G K F B
        (extendSupportedGenericPairPattern B S q) (select q) :=
    Classical.choose_spec (hChoose q)
  have hRestrict (q : Pattern) :
      genericPairColourOn B S (select q) = q := by
    funext p
    obtain ⟨hOrd, i, j, hi, hj⟩ :=
      hRepresented p.val p.property
    have hNumOrd : p.val.1.val < p.val.2.val := hOrd
    have hTargetOrd : F i < F j := by
      rw [hi, hj]
      exact hNumOrd
    have hTargetCut : F j < B := by
      rw [hj]
      exact p.val.2.isLt
    obtain ⟨t, _htN, _htM, _htB, _htLeaf, hCol, hPat⟩ :=
      hCofinal q 0 0
    have hBit :
        (K.edge p.val.1.val p.val.2.val (F t) ↔
          q p = true) := by
      have h := hPat i j hTargetOrd hTargetCut
      rw [hi, hj] at h
      simpa only [extendSupportedGenericPairPattern_at] using h
    have hMask :
        (select q) p.val.1 p.val.2 =
          decide (K.edge p.val.1.val p.val.2.val (F t)) := by
      rw [← hCol]
      simp [DiaryLowerBoundColors.singletonColour, hNumOrd]
    change (select q) p.val.1 p.val.2 = q p
    rw [hMask]
    cases hq : q p <;> simp_all [hq]
  have hInjective : Function.Injective select := by
    intro q r hEq
    calc
      q = genericPairColourOn B S (select q) :=
        (hRestrict q).symm
      _ = genericPairColourOn B S (select r) :=
        congrArg (genericPairColourOn B S) hEq
      _ = r := hRestrict r
  exact ⟨select, hInjective, hCofinal, hRestrict⟩

end DiaryLeafPriority
end ThreeUniformDiaries
