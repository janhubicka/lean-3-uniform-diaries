import ThreeUniformDiaries.GenericExtensionStep

/-!
# An explicit enumerated generic 3-uniform hypergraph exists

The existing GenericEnumerated3Graph API takes an actual ordered graph
and assumes its finite initial-segment extension property. The upper
Ramsey theorems had so far carried an explicit G parameter. We now
construct one concrete G with **no genericity existence assumption**.

Use Nat.pair m code to enumerate all finite patterns on pairs of the
first m vertices. The left pairing coordinate satisfies
m ≤ Nat.pair m code. Decode the second coordinate as the finite set
of ordered pairs on Fin m whose incident triple is an edge. For any
specified pattern, choose the vertex encoding exactly that finite set.
Nat.unpair_pair and Encodable.encodek prove its prescribed adjacency
table verbatim.

All actual edges are restricted to increasing triples; missing
or undecodable codes simply produce nonedges. No Fraïssé limit,
choice of an unspecified generic graph, or Ramsey theorem is used.
-/

namespace ThreeUniformDiaries

/-- Encode an increasing edge (a,b,c) through the finite pair-pattern
stored in the Nat.unpair code of its last vertex c. -/
noncomputable def pairCodedGenericEdge (a b c : Nat) : Prop := by
  classical
  let m := (Nat.unpair c).1
  exact a < b ∧ b < c ∧
    (if ha : a < m then
      if hb : b < m then
        (⟨a,ha⟩,⟨b,hb⟩) ∈
          ((Encodable.decode (Nat.unpair c).2 :
            Option (Finset (Fin m × Fin m))).getD ∅)
      else False
    else False)

/-- A concrete witness to the full enumerated generic extension
property, not merely a finite-stage source embedding. -/
noncomputable def canonicalGenericEnumerated3Graph :
    GenericEnumerated3Graph where
  graph := ⟨pairCodedGenericEdge⟩
  extension := by
    classical
    intro m pattern
    let S : Finset (Fin m × Fin m) :=
      Finset.univ.filter
        (fun p => p.1 < p.2 ∧ pattern p.1 p.2 = true)
    let v : Nat := Nat.pair m (Encodable.encode S)
    have hvm : m ≤ v := Nat.left_le_pair m (Encodable.encode S)
    refine ⟨v, hvm, ?_⟩
    intro i j hij
    have hJV : j.val < v := lt_of_lt_of_le j.isLt hvm
    have hS : (i,j) ∈ S ↔ pattern i j = true := by
      simp [S, hij]
    have hDecode :
        (Encodable.decode (Encodable.encode S) :
          Option (Finset (Fin m × Fin m))) = some S :=
      Encodable.encodek S
    change pairCodedGenericEdge i.val j.val v ↔
      pattern i j = true
    calc
      pairCodedGenericEdge i.val j.val v ↔ (i,j) ∈ S := by
        simp [pairCodedGenericEdge, v, Nat.unpair_pair,
          hij, hJV, i.isLt, j.isLt, hDecode]
        rfl
      _ ↔ pattern i j = true := hS

/-- There exists at least one actual enumerated generic 3-hypergraph.
Thus a theorem quantified over G can be instantiated without
postulating a generic existence axiom. -/
theorem nonempty_genericEnumerated3Graph :
    Nonempty GenericEnumerated3Graph :=
  ⟨canonicalGenericEnumerated3Graph⟩

end ThreeUniformDiaries
