import ThreeUniformDiaries.DiaryGenericE5NestedHorizonNoCompactness
import ThreeUniformDiaries.DiaryGenericMixedConeIndivisibility

/-!
# Track D: a FIXED full singleton colour AND old E5 mask still do not
# give a persistent leaf through nested whole-generic horizon tails

The preceding genuine generic-E5 horizon no-compactness theorem shows
that one fixed old-pair E5 mask q and a WHOLE induced generic copy
in EACH nested finite-horizon tail do not select one persistent v.

We now strengthen the test to a FIXED COMPLETE FINITE SINGLETON
COLOUR c below ANY prescribed finite cut B, selected ONCE BEFORE
ALL future horizon cutoffs M.

Proof: first choose an ordered induced whole generic selfcopy p
realizing q on every protected old-pair with every protected old
vertex below the image. Apply the already kernel-verified finite
vertex-colour Ramsey theorem inside that WHOLE p-copy, obtaining
another induced generic selfembedding w and ONE complete mixed
singleton colour c of the actual G.graph below B, constant
at p(w i). For ANY future target cutoff M, choose a further
induced generic selfembedding v with source images sufficiently
late to force p(w(v i))>M. The composition p∘w∘v is still an
ordered induced G-copy, still realizes the same q and the SAME c.

Every horizon tail in this one fixed colour contains a complete
generic selfcopy; every finite intersection does as well. But no
fixed v can survive ALL future horizon lower bounds M<v.

The final G-embedding is NOT claimed auxiliary-type-respecting:
the first old-E5 fibre embedding need not preserve auxiliary types.
This is a leaf-only generic graph compactness countermodel, NOT an
actual RoleDiary reserved-stage counterexample and NOT a refutation
of countable diary unavoidability. The source-required S1/S2 and
E2/E3 split data and literal old-f compatibility are still missing.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For any genuine enumerated generic G, finite protected old
set A, arbitrary fixed old E5 Boolean mask q, and complete
singleton-type cut B, choose ONE actual finite mask c such that
FOR EVERY future horizon M there is a WHOLE ordered induced
generic selfcopy whose every vertex:
  * lies above M and every old a∈A;
  * realizes the SAME fixed q on EVERY protected old pair;
  * has the SAME complete singleton-colour c below B.

Moreover NO single vertex realizes these horizon constraints for
all M, even in the selected fixed colour c. Thus infinite generic
reservoirs and full finite colouring stabilization do not
substitute for a bounded-image/persistent successor lemma. -/
theorem GenericEnumerated3Graph.exists_fixed_colour_generic_oldPair_tails_without_persistent_image
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool) (B : Nat) :
    ∃ c : Fin B → Fin B → Bool,
      (∀ M : Nat,
        ∃ u : Ordered3Graph.Embedding G.graph G.graph,
          ∀ i : Nat,
            GenericOldPairHorizonTail G A q M (u i) ∧
            DiaryLowerBoundColors.singletonColour G.graph B (u i) = c) ∧
      ¬ (∃ x : Nat,
        ∀ M : Nat,
          GenericOldPairHorizonTail G A q M x ∧
          DiaryLowerBoundColors.singletonColour G.graph B x = c) := by
  classical
  obtain ⟨p, _hPAfter0, hPAboveA, hPPattern⟩ :=
    _root_.ThreeUniformDiaries.DiaryLeafPriority.GenericEnumerated3Graph.exists_induced_generic_selfcopy_in_oldPair_fibre G
      A q 0
  obtain ⟨w, _hWAux, c, hColour⟩ :=
    exists_generic_selfcopy_in_one_mixed_singleton_cone
      G G.graph B (fun i : Nat => p i)
  have hCompInjective :
      Function.Injective (fun i : Nat => p (w i)) :=
    p.strictMono.injective.comp w.strictMono.injective
  refine ⟨c, ?_, ?_⟩
  · intro M
    obtain ⟨N, hLarge⟩ :=
      injective_nat_eventually_above_bound
        (fun i : Nat => p (w i)) hCompInjective M
    obtain ⟨v, hVAfter, _hVOld, _hVPattern⟩ :=
      _root_.ThreeUniformDiaries.DiaryLeafPriority.GenericEnumerated3Graph.exists_induced_generic_selfcopy_in_oldPair_fibre G
        (∅ : Finset Nat) (fun _ _ => false) N
    let u : Ordered3Graph.Embedding G.graph G.graph := {
      toFun := fun i : Nat => p (w (v i))
      strictMono := by
        intro i j hij
        exact p.strictMono (w.strictMono (v.strictMono hij))
      edge_iff := by
        intro a b d hab hbd
        exact (v.edge_iff hab hbd).trans
          ((w.edge_iff (v.strictMono hab) (v.strictMono hbd)).trans
            (p.edge_iff (w.strictMono (v.strictMono hab))
              (w.strictMono (v.strictMono hbd))))
    }
    refine ⟨u, ?_⟩
    intro i
    have hAbove : M < p (w (v i)) :=
      hLarge (v i) (Nat.le_of_lt (hVAfter i))
    have hMask :
        DiaryLowerBoundColors.singletonColour G.graph B
          (p (w (v i))) = c :=
      hColour (v i)
    change GenericOldPairHorizonTail G A q M (p (w (v i))) ∧
      DiaryLowerBoundColors.singletonColour G.graph B
        (p (w (v i))) = c
    exact ⟨⟨hAbove,
      (fun a ha => hPAboveA (w (v i)) a ha),
      (fun a b ha hb hab => hPPattern (w (v i)) a b ha hb hab)⟩,
      hMask⟩
  · rintro ⟨x, hx⟩
    exact generic_oldPairHorizonTail_no_persistent_image
      G A q ⟨x, (fun M => (hx M).1)⟩

end DiaryLeafPriority
end ThreeUniformDiaries
