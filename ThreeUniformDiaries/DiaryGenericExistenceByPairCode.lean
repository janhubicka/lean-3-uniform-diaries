import ThreeUniformDiaries.GenericExtensionStep

/-!
# Explicit existence of an enumerated generic 3-uniform hypergraph

Every finite Boolean pattern on pairs below m is encoded as an ordinary
finite set of pairs of natural numbers. Put that finite set's encoded
number into the second component of Nat.pair m code. The pairing
function makes the new vertex v at least m, and Nat.unpair recovers
the encoded finite adjacency table.

We deliberately decode an ordinary Finset (Nat × Nat), rather than
a dependent Finset (Fin m × Fin m). This avoids transporting finite
index types through the equalities for Nat.unpair_pair. No abstract
generic existence assumption or Ramsey theorem is used.
-/

namespace ThreeUniformDiaries

/-- A 3-edge is read from the ordinary finite pair table encoded
in its greatest vertex, with the increasing-triple condition explicit. -/
noncomputable def pairCodedGenericEdge (a b c : Nat) : Prop :=
  a < b ∧ b < c ∧
    (a,b) ∈ ((Encodable.decode (Nat.unpair c).2 :
      Option (Finset (Nat × Nat))).getD ∅)

/-- An actual generically extendible enumerated 3-hypergraph. -/
noncomputable def canonicalGenericEnumerated3Graph :
    GenericEnumerated3Graph where
  graph := ⟨pairCodedGenericEdge⟩
  extension := by
    classical
    intro m pattern
    let S : Finset (Nat × Nat) :=
      ((Finset.univ : Finset (Fin m × Fin m)).filter
        (fun p => p.1 < p.2 ∧ pattern p.1 p.2 = true)).image
        (fun p => (p.1.val, p.2.val))
    let v : Nat := Nat.pair m (Encodable.encode S)
    have hvm : m ≤ v := Nat.left_le_pair m (Encodable.encode S)
    refine ⟨v, hvm, ?_⟩
    intro i j hij
    have hJV : j.val < v := lt_of_lt_of_le j.isLt hvm
    have hS : (i.val,j.val) ∈ S ↔ pattern i j = true := by
      constructor
      · intro h
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
        have hi : p.1 = i := Fin.ext (congrArg Prod.fst heq)
        have hj : p.2 = j := Fin.ext (congrArg Prod.snd heq)
        have hbit : pattern p.1 p.2 = true :=
          (Finset.mem_filter.mp hp).2.2
        simpa only [hi,hj] using hbit
      · intro h
        apply Finset.mem_image.mpr
        refine ⟨(i,j), ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ⟨hij, h⟩⟩
    have hDecode :
        (Encodable.decode (Encodable.encode S) :
          Option (Finset (Nat × Nat))) = some S :=
      Encodable.encodek S
    change pairCodedGenericEdge i.val j.val v ↔
      pattern i j = true
    calc
      pairCodedGenericEdge i.val j.val v ↔
          (i.val,j.val) ∈ S := by
        simp [pairCodedGenericEdge, v, Nat.unpair_pair,
          hij, hJV, hDecode]
      _ ↔ pattern i j = true := hS

/-- A concrete enumerated generic hypergraph exists, rather than
only a structure parametrised by an unproved extension property. -/
theorem nonempty_genericEnumerated3Graph :
    Nonempty GenericEnumerated3Graph :=
  ⟨canonicalGenericEnumerated3Graph⟩

end ThreeUniformDiaries
