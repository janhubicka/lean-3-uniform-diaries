import ThreeUniformDiaries.InfiniteCanonicalSelectedPairs

/-!
# The infinite canonical enumeration map preserves selected triples

The concrete E0 map introduces each new source hyperedge (i,j,k)
at the selected target triple (f(i),f(j),f(k)). The new hyperedge
parameter is exactly the already constructed E1 boundary one-type
map, whose selected pairs are now proved preserved.

Earlier source triples persist through selected E0 truncation.
This establishes the induced enumerated-hypergraph embedding
property of the ACTUAL infinite canonical enumeration map, not an
abstract CanonicalMap compatibility hypothesis.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteEnumCanonicalMap_newTriple
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (k i j : Nat) (hij : i < j) (hjk : j < k)
    (a : EnumNode (k + 1)) :
    (infiniteEnumCanonicalMap h₀ h₁ h₂ (k + 1) a).val.triple
      (f i) (f j) (f k) = a.triple i j k := by
  have hcone := infiniteEnumCanonicalMap_succ
    h₀ h₁ h₂ k (a.truncate k) (a.boundaryOne k)
  rw [EnumNode.succ_truncate_boundary] at hcone
  have hcut := hcone.2
  change CoordNode.enum (f k + 1)
      ((infiniteEnumCanonicalMap h₀ h₁ h₂ (k + 1) a).val.truncate
        (f k + 1)) =
    CoordNode.enum (f k + 1)
      ((infiniteEnumCanonicalMap h₀ h₁ h₂ k (a.truncate k)).val.succ
       (infiniteOneCanonicalMap h₁ h₂ k (a.boundaryOne k)).val) at hcut
  have hbit := congrArg
    (fun x : CoordNode =>
      match x with
      | .enum _ b => b.triple (f i) (f j) (f k)
      | _ => false) hcut
  have htriple :
      (infiniteEnumCanonicalMap h₀ h₁ h₂ (k + 1) a).val.triple
        (f i) (f j) (f k) =
      (infiniteOneCanonicalMap h₁ h₂ k (a.boundaryOne k)).val.pair
        (f i) (f j) := by
    simpa [CoordNode.truncate, EnumNode.truncate,
      EnumNode.succ, Nat.lt_succ_self] using hbit
  have hone :=
    infiniteOneCanonicalMap_selectedPair h₁ h₂ hf k i j hij hjk
      (a.boundaryOne k)
  calc
    (infiniteEnumCanonicalMap h₀ h₁ h₂ (k + 1) a).val.triple
        (f i) (f j) (f k) =
      (infiniteOneCanonicalMap h₁ h₂ k (a.boundaryOne k)).val.pair
        (f i) (f j) := htriple
    _ = (a.boundaryOne k).pair i j := hone
    _ = a.triple i j k := by
      simp [EnumNode.boundaryOne, hij, hjk]

theorem infiniteEnumCanonicalMap_selectedTriple
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) :
    ∀ (N i j k : Nat) (hij : i < j) (hjk : j < k)
      (hkN : k < N) (a : EnumNode N),
      (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val.triple
        (f i) (f j) (f k) = a.triple i j k := by
  intro N
  induction N with
  | zero =>
      intro i j k hij hjk hkN a
      omega
  | succ l ih =>
      intro i j k hij hjk hkN a
      by_cases hlast : k = l
      · subst k
        exact infiniteEnumCanonicalMap_newTriple
          h₀ h₁ h₂ hf l i j hij hjk a
      · have hkl : k < l := by omega
        have hparent := infiniteEnumCanonicalMap_parent h₀ h₁ h₂ l a
        have hb := congrArg
          (fun x : EnumNode (f l) => x.triple (f i) (f j) (f k)) hparent
        have hfk : f k < f l := hf hkl
        have hprev :
            (infiniteEnumCanonicalMap h₀ h₁ h₂ (l + 1) a).val.triple
              (f i) (f j) (f k) =
            (infiniteEnumCanonicalMap h₀ h₁ h₂ l (a.truncate l)).val.triple
              (f i) (f j) (f k) := by
          simpa [EnumNode.truncate, hfk] using hb
        calc
          (infiniteEnumCanonicalMap h₀ h₁ h₂ (l + 1) a).val.triple
              (f i) (f j) (f k) =
            (infiniteEnumCanonicalMap h₀ h₁ h₂ l (a.truncate l)).val.triple
              (f i) (f j) (f k) := hprev
          _ = (a.truncate l).triple i j k :=
            ih i j k hij hjk hkl (a.truncate l)
          _ = a.triple i j k := by simp [EnumNode.truncate, hkl]

end CoordNode
end ThreeUniformDiaries
