import ThreeUniformDiaries.DiaryGenericMixedConeIndivisibility
import ThreeUniformDiaries.DiarySingletonColourCofinalCone

/-!
# Track C: one finite colour supports generic subcopies arbitrarily far out

English proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #306

Let rho colour the vertices of the ACTUAL enumerated generic
3-uniform hypergraph G by an arbitrary finite nonempty palette.
Let F be ANY injective numerical map, with no order-preservation
hypothesis. There is ONE colour c, selected BEFORE the target
numerical cutoff M, such that beyond EVERY M the colour-c fibre
contains an induced auxiliary-type-respecting generic selfcopy.

For a given cutoff M, apply the verified finite vertex-colour
indivisibility theorem to the product of rho and the Boolean
test M < F(n). An injective image of a whole generic selfcopy
cannot be numerically bounded, so the winning Boolean bit is TRUE.
Then finite downward choice fixes the SAME winning rho-colour for
all target bounds. The selfcopies may differ with M.

No specified colour, no prescribed diary split profile, no future
horizon persistence, and no countable diary unavoidability is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finite vertex colour of the generic 3-uniform hypergraph has
ONE colour class containing induced generic subcopies arbitrarily far
out under ANY injective outer numerical map F.

The winning colour is fixed before every numerical bound M. Each
selfembedding is genuinely induced and AuxTypeRespecting, not merely
an infinite set of monochromatic vertices. F need not be monotone.
This is a finite-palette Ramsey consequence, not a saturation or
persistent-leaf-image principle. -/
theorem exists_uniform_cofinal_generic_monochromatic_subcopies
    (G : GenericEnumerated3Graph)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (rho : Nat → κ) (F : Nat → Nat)
    (hF : Function.Injective F) :
    ∃ c : κ,
      ∀ M : Nat,
        ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
          u.AuxTypeRespecting ∧
          ∀ n : Nat, M < F (u n) ∧ rho (u n) = c := by
  classical
  let R : κ → Nat → Prop := fun c M =>
    ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
      u.AuxTypeRespecting ∧
      ∀ n : Nat, M < F (u n) ∧ rho (u n) = c
  have hDown : ∀ c : κ, ∀ N M : Nat,
      M ≤ N → R c N → R c M := by
    intro c N M hMN
    rintro ⟨u, hu, hAll⟩
    refine ⟨u, hu, ?_⟩
    intro n
    obtain ⟨hHigh, hColour⟩ := hAll n
    exact ⟨lt_of_le_of_lt hMN hHigh, hColour⟩
  have hCover : ∀ M : Nat,
      ∃ c : κ, c ∈ (Finset.univ : Finset κ) ∧ R c M := by
    intro M
    let colour : Nat → κ × Bool :=
      fun n => (rho n, decide (M < F n))
    obtain ⟨u, hu, ⟨c, flag⟩, hMono⟩ :=
      generic_finite_vertex_colouring_monochromatic G colour
    have hInjective : Function.Injective (fun n : Nat => F (u n)) :=
      hF.comp u.strictMono.injective
    obtain ⟨N, hEventually⟩ :=
      injective_nat_eventually_above_bound
        (fun n : Nat => F (u n)) hInjective M
    have hFlagAtN : decide (M < F (u N)) = flag := by
      have h := congrArg (fun z : κ × Bool => z.2) (hMono N)
      change decide (M < F (u N)) = flag at h
      exact h
    have hFlagTrue : flag = true := by
      have hYes : decide (M < F (u N)) = true := by
        simp [hEventually N (le_refl N)]
      exact hFlagAtN.symm.trans hYes
    have hAll (n : Nat) :
        M < F (u n) ∧ rho (u n) = c := by
      have h := hMono n
      have hColour :
          rho (u n) = c := by
        have hh := congrArg (fun z : κ × Bool => z.1) h
        change rho (u n) = c at hh
        exact hh
      have hBit : decide (M < F (u n)) = flag := by
        have hh := congrArg (fun z : κ × Bool => z.2) h
        change decide (M < F (u n)) = flag at hh
        exact hh
      have hDec : decide (M < F (u n)) = true :=
        hBit.trans hFlagTrue
      have hHigh : M < F (u n) := by
        by_cases hn : M < F (u n)
        · exact hn
        · simp [hn] at hDec
      exact ⟨hHigh, hColour⟩
    exact ⟨c, Finset.mem_univ _, u, hu, hAll⟩
  obtain ⟨c, _hc, hAll⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset κ) R hDown hCover
  exact ⟨c, hAll⟩

end DiaryLeafPriority
end ThreeUniformDiaries
