import ThreeUniformDiaries.DiaryFiniteATRFamily
import ThreeUniformDiaries.DiaryFinitePointedEnvelope
import ThreeUniformDiaries.DiaryFiniteSingletonEnvelope

/-!
# A finite universe of all small enumerated ATR source shapes

At any protected cut n, every singleton envelope has n+1 actual
vertices, and every pointed pair envelope has n+2 or n+3 actual
vertices. Each finite enumerated 3-hypergraph is completely
determined by its Boolean triple mask on the finite vertex set;
the out-of-range/non-increasing triples are forced to false.

This gives a finite list of ALL possible source EnumNodes in the
three required sizes. It may contain shapes having no admissible
embedding into the generic graph, but the unconditional finite ATR
theorem explicitly handles those cases vacuously. We therefore do
not need to assume or construct particular pair-type representatives.

The list is a common source universe for finite-family
singleton/pair stabilisation at one cut.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

/-- An EnumNode on a fixed finite level has a finite type: it injects
into the finite Boolean array of triples on Fin n. -/
noncomputable instance enumNodeFintype (n : Nat) :
    Fintype (EnumNode n) := by
  classical
  let f : EnumNode n → (Fin n → Fin n → Fin n → Bool) :=
    fun A x y z => A.triple x.val y.val z.val
  apply Fintype.ofInjective f
  intro A B h
  apply EnumNode.ext_triples
  funext i j k
  by_cases hvalid : i < j ∧ j < k ∧ k < n
  · have hi : i < n := by omega
    have hj : j < n := by omega
    have hk : k < n := hvalid.2.2
    have hval := congrFun
      (congrFun
        (congrFun h (⟨i, hi⟩ : Fin n))
        (⟨j, hj⟩ : Fin n))
      (⟨k, hk⟩ : Fin n)
    simpa only [f] using hval
  · exact (A.support i j k hvalid).trans
      (B.support i j k hvalid).symm

/-- An arbitrary n+1-vertex singleton source as a protected
finite-family ATR source. -/
def oneVertexSource (n : Nat) (A : EnumNode (n+1)) :
    ProtectedSource n :=
  ⟨n, A, by omega⟩

/-- An arbitrary n+2-vertex pointed two-tail source. -/
def twoVertexSource (n : Nat) (A : EnumNode (n+2)) :
    ProtectedSource n :=
  ⟨n+1, A, by omega⟩

/-- An arbitrary n+3-vertex pointed three-tail source. -/
def threeVertexSource (n : Nat) (A : EnumNode (n+3)) :
    ProtectedSource n :=
  ⟨n+2, A, by omega⟩

/-- Finite universal list: all actual source shapes with one,
two, or three vertices outside the protected cut. -/
noncomputable def smallSourceUniverse (n : Nat) :
    List (ProtectedSource n) := by
  classical
  exact
    ((Finset.univ : Finset (EnumNode (n+1))).toList.map
      (oneVertexSource n)) ++
    ((Finset.univ : Finset (EnumNode (n+2))).toList.map
      (twoVertexSource n)) ++
    ((Finset.univ : Finset (EnumNode (n+3))).toList.map
      (threeVertexSource n))

theorem oneVertexSource_mem
    (n : Nat) (A : EnumNode (n+1)) :
    oneVertexSource n A ∈ smallSourceUniverse n := by
  classical
  unfold smallSourceUniverse
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  exact List.mem_map.mpr ⟨A, by simp, rfl⟩

theorem twoVertexSource_mem
    (n : Nat) (A : EnumNode (n+2)) :
    twoVertexSource n A ∈ smallSourceUniverse n := by
  classical
  unfold smallSourceUniverse
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨A, by simp, rfl⟩

theorem threeVertexSource_mem
    (n : Nat) (A : EnumNode (n+3)) :
    threeVertexSource n A ∈ smallSourceUniverse n := by
  classical
  unfold smallSourceUniverse
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨A, by simp, rfl⟩

/-- Simultaneous ATR homogeneity over EVERY possible finite
singleton/pair source shape on at most three exterior vertices.
The colours may depend on the source and see only actual finite
embedding images. No class-specific representative selection is
assumed for the pair shapes. -/
theorem actualFiniteAuxRamsey_smallSourceUniverse
    (G : GenericEnumerated3Graph) (n : Nat)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : ∀ A : ProtectedSource n, A.Code G → κ) :
    ∃ (u : Ordered3Graph.Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      ∀ A ∈ smallSourceUniverse n,
        ∃ color : κ, ∀ e : A.Code G,
          A.FixesPrefix G e →
          χ A (e.postcompose u hu) = color := by
  exact actualFiniteAuxRamsey_finiteFamily
    G n χ (smallSourceUniverse n)

end ATRFiniteDecoder
end ThreeUniformDiaries
