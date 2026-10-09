import ThreeUniformDiaries.ActualFiniteEmbeddingMeets

/-!
# A finite aux-type-respecting embedding need not extend globally

This is a concrete counterexample to an unjustified step in the
formalisation of manuscript Lemma Aemb: replacing a finite embedding
by an aux-type-respecting embedding of both graphs after infinitely
many artificial zero-edge vertices have been appended.

Take the one-vertex empty source and a target with the single edge
(0,1,3). Map source vertex 0 to target vertex 3. As a finite
one-vertex embedding, the aux-type conditions are vacuous. But if
any increasing embedding fixes 0 -> 3, the artificially added source
vertex 1 has the same singleton type as 0 below source cut 0,
whereas target 3 has the edge (0,1,3) and every larger vertex lacks
that edge. No global aux-type-respecting extension exists.

This does not refute Aemb; it demonstrates why it needs its genuine
finite-only type hypothesis, as formalised in ActualFiniteEmbeddingMeets.
-/

namespace ThreeUniformDiaries

private def scopedSource : Ordered3Graph Nat where
  edge _ _ _ := False

private def scopedTarget : Ordered3Graph Nat where
  edge a b c := a = 0 ∧ b = 1 ∧ c = 3

private def scopedShift (i : Nat) : Nat := i + 3

private theorem scopedShift_strictMono : StrictMono scopedShift := by
  intro a b hab
  dsimp [scopedShift]
  omega

/-- The chosen map is an induced embedding of the infinitely
zero-extended source graph: all its images are >= 3. -/
private def scopedGlobalEmbedding :
    Ordered3Graph.Embedding scopedSource scopedTarget where
  toFun := scopedShift
  strictMono := scopedShift_strictMono
  edge_iff := by
    intro a b c hab hbc
    constructor
    · intro h
      exact False.elim h
    · rintro ⟨ha, hb, hc⟩
      dsimp [scopedShift] at ha
      omega

/-- Its finite one-vertex restriction satisfies the actual finite
aux-type-respecting conditions. -/
theorem scopedExample_finiteAuxEmbedding :
    Ordered3Graph.FiniteAuxEmbedding
      scopedSource scopedTarget scopedShift 1 := by
  refine ⟨scopedShift_strictMono, ?_, ?_, ?_⟩
  · intro a b c hab hbc hc
    exfalso
    omega
  · intro w u v hwu hwv hu hv
    have huv : u = v := by omega
    subst v
    constructor
    · intro _
      intro a b hab hb
      exact Iff.rfl
    · intro _
      intro a b hab hb
      exact Iff.rfl
  · intro w u₀ u₁ v₀ v₁ hwu hu hwv hv hu₁ hv₁
    exfalso
    omega

/-- Yet the induced zero-extension embedding is NOT globally
aux-type-respecting: its source's artificial vertex 1 is the
witness. -/
theorem scopedExample_not_global_auxTypeRespecting :
    ¬ scopedGlobalEmbedding.AuxTypeRespecting := by
  intro haux
  have hsource :
      scopedSource.SameOneTypeBelow 0 0 1 := by
    intro a b hab hb
    omega
  have htarget :=
    (haux.one 0 0 1 (Nat.zero_le 0) (Nat.zero_le 1)).mp
      hsource
  have hbit : scopedTarget.edge 0 1 (scopedGlobalEmbedding 0) ↔
      scopedTarget.edge 0 1 (scopedGlobalEmbedding 1) :=
    htarget (by decide) (by decide)
  have hleft : scopedTarget.edge 0 1 (scopedGlobalEmbedding 0) := by
    simp [scopedGlobalEmbedding, scopedShift, scopedTarget]
  have hright :
      ¬ scopedTarget.edge 0 1 (scopedGlobalEmbedding 1) := by
    simp [scopedGlobalEmbedding, scopedShift, scopedTarget]
  exact hright (hbit.mp hleft)

/-- More strongly, NO order-preserving global aux-type-respecting
embedding with first image 3 exists in this target, independently
of how all later artificial source vertices are chosen. -/
theorem scopedExample_no_global_aux_extension
    (e : Ordered3Graph.Embedding scopedSource scopedTarget)
    (he0 : e 0 = 3) :
    ¬ e.AuxTypeRespecting := by
  intro haux
  have hsource :
      scopedSource.SameOneTypeBelow 0 0 1 := by
    intro a b hab hb
    omega
  have htarget :=
    (haux.one 0 0 1 (Nat.zero_le 0) (Nat.zero_le 1)).mp
      hsource
  have hlt : 3 < e 1 := by
    have h := e.strictMono (Nat.zero_lt_one)
    rw [he0] at h
    exact h
  have hbit : scopedTarget.edge 0 1 (e 0) ↔
      scopedTarget.edge 0 1 (e 1) :=
    htarget (by decide) (by rw [he0]; decide)
  have hleft : scopedTarget.edge 0 1 (e 0) := by
    simp [scopedTarget, he0]
  have hright : ¬ scopedTarget.edge 0 1 (e 1) := by
    simp only [scopedTarget]
    omega
  exact hright (hbit.mp hleft)

end ThreeUniformDiaries
