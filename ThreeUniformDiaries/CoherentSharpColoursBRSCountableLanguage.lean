import ThreeUniformDiaries.CoherentSharpColoursBRSProfiles
import ThreeUniformDiaries.DiaryFiniteATRShapeUniverse

/-!
# Countable relational signature of the abstract BRS expansion

A coherent finite-colour system has a finite palette for each
enumerated finite hypergraph. There are countably many finite
source arities, finitely many EnumNode sources at each arity,
and finitely many colours per source. Therefore the family of
arity-indexed new relation symbols is COUNTABLE.

This verifies the language-size requirement of the abstract
Hubicka--Zucker BRS construction: no fixed arity bound or finite
relational language is asserted.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder
namespace CoherentFiniteColourSystem

variable {U : Ordered3Graph Nat} (C : CoherentFiniteColourSystem U)

/-- Abstract BRS relation symbols form a countable type:
Sigma over arity, finite enumerated source and finite colour. -/
noncomputable instance relationSymbolCountable :
    Countable (C.RelationSymbol) := by
  classical
  letI (n : Nat) (A : EnumNode n) : Finite (C.Palette n A) :=
    C.finitePalette A
  letI (n : Nat) (A : EnumNode n) : Countable (C.Palette n A) :=
    inferInstance
  letI : Countable (Σ n : Nat, Σ A : EnumNode n,
    C.Palette n A) := inferInstance
  obtain ⟨encode, hEncode⟩ :=
    (countable_iff_exists_injective
      (Σ n : Nat, Σ A : EnumNode n, C.Palette n A)).mp
        (by infer_instance)
  apply (countable_iff_exists_injective (C.RelationSymbol)).mpr
  refine ⟨(fun σ : C.RelationSymbol =>
      encode (⟨σ.arity, ⟨σ.source, σ.colour⟩⟩ :
        Σ n : Nat, Σ A : EnumNode n, C.Palette n A)), ?_⟩
  intro s t h
  have heq :
      (⟨s.arity, ⟨s.source, s.colour⟩⟩ :
        Σ n : Nat, Σ A : EnumNode n, C.Palette n A) =
      (⟨t.arity, ⟨t.source, t.colour⟩⟩ :
        Σ n : Nat, Σ A : EnumNode n, C.Palette n A) :=
    hEncode h
  cases s with
  | mk sn sA sd =>
    cases t with
    | mk tn tA td =>
      cases heq
      rfl

end CoherentFiniteColourSystem
end ATRFiniteDecoder
end ThreeUniformDiaries
