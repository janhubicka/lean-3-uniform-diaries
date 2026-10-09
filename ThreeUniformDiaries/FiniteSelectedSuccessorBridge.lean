import ThreeUniformDiaries.ActualFiniteEmbeddingMeets
import ThreeUniformDiaries.TypeNodePrefix

/-!
# Boundary successor compatibility for finite Aemb coding

For two consecutive *selected* cuts f(i) < f(i+1), the type nodes
at the later cut may contain arbitrary information on skipped target
vertices. Their prefix at f(i)+1 is nevertheless the prescribed
immediate successor of the earlier type node. In the auxiliary
coordinate its new bit is the source edge by the finite induced
embedding condition.

These three concrete successor identities are the local missing
interface in the simultaneous canonical-map induction of manuscript
Lemma Aemb. They do not assume a globally aux-respecting embedding
of an artificially zero-extended finite source.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- Across any nonempty gap of levels, an auxiliary type restricts
to the immediate successor determined by its actual boundary bit. -/
theorem auxType_gap_succ
    {N a b u v : Nat} (H : EnumNode N) (hab : a + 1 ≤ b) :
    (H.auxType b u v).truncate (a + 1) =
      (H.auxType a u v).succ (H.triple a u v) := by
  rw [H.auxType_truncate (u := u) (v := v) hab]
  apply AuxNode.ext_bits
  funext x
  exact H.auxType_succ_bit (l := a) (u := u) (v := v) (i := x)

/-- The boundary successor parameter in the 1-type coordinate is
the auxiliary type of the new ordinary vertex and the type vertex. -/
theorem oneType_gap_succ
    {N a b v : Nat} (H : EnumNode N) (hab : a + 1 ≤ b) :
    (H.oneType b v).truncate (a + 1) =
      (H.oneType a v).succ (H.auxType a a v) := by
  rw [H.oneType_truncate (u := v) hab]
  apply OneNode.ext_pairs
  funext x y
  exact H.oneType_succ_pair (l := a) (v := v) (i := x) (j := y)

/-- The boundary successor parameter in the enumeration coordinate
is the singleton type of the new ordinary vertex. -/
theorem enum_gap_succ
    {N a b : Nat} (H : EnumNode N) (hab : a + 1 ≤ b) :
    (H.truncate b).truncate (a + 1) =
      (H.truncate a).succ (H.oneType a a) := by
  rw [H.truncate_truncate hab]
  apply EnumNode.ext_triples
  funext x y z
  exact H.truncate_succ_triple (l := a) (i := x) (j := y) (k := z)

/-- For a genuine finite induced embedding, the bit governing the
auxiliary successor at selected vertex i is exactly A(i,u,v). -/
theorem finite_selected_aux_edge_bit
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (i u v : Nat)
    (hiu : i < u) (huv : u < v) (hvm : v < m) :
    H.triple (f i) (f u) (f v) = A.triple i u v := by
  have he := hf.edge_iff i u v hiu huv hvm
  change (A.triple i u v = true ↔
    H.triple (f i) (f u) (f v) = true) at he
  cases ha : A.triple i u v <;>
    cases hb : H.triple (f i) (f u) (f v) <;>
    simp_all

/-- At consecutive selected levels, the concrete E2 type nodes
meet the immediate successor prescribed by the finite source A,
despite all omitted target levels in between. -/
theorem finite_selected_aux_successor
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (i u v : Nat)
    (hiu : i < u) (huv : u < v) (hvm : v < m) :
    (H.auxType (f (i + 1)) (f u) (f v)).truncate (f i + 1) =
      (H.auxType (f i) (f u) (f v)).succ
        (A.triple i u v) := by
  have hlt : f i < f (i + 1) :=
    hf.strictMono (Nat.lt_succ_self i)
  have hstep : f i + 1 ≤ f (i + 1) := by omega
  calc
    (H.auxType (f (i + 1)) (f u) (f v)).truncate (f i + 1) =
        (H.auxType (f i) (f u) (f v)).succ
          (H.triple (f i) (f u) (f v)) :=
      H.auxType_gap_succ hstep
    _ = (H.auxType (f i) (f u) (f v)).succ (A.triple i u v) := by
      rw [finite_selected_aux_edge_bit A H f hf i u v hiu huv hvm]

/-- The parallel 1-type boundary successor: its parameter is
the selected auxiliary node for the pair i,v. -/
theorem finite_selected_one_successor
    {N : Nat} (H : EnumNode N) (f : Nat → Nat)
    (hf : StrictMono f) (i v : Nat) :
    (H.oneType (f (i + 1)) (f v)).truncate (f i + 1) =
      (H.oneType (f i) (f v)).succ
        (H.auxType (f i) (f i) (f v)) := by
  have hlt : f i < f (i + 1) := hf (Nat.lt_succ_self i)
  have hstep : f i + 1 ≤ f (i + 1) := by omega
  exact H.oneType_gap_succ hstep

/-- The enumeration boundary is likewise determined by the selected
singleton-type node at cut i. -/
theorem finite_selected_enum_successor
    {N : Nat} (H : EnumNode N) (f : Nat → Nat)
    (hf : StrictMono f) (i : Nat) :
    (H.truncate (f (i + 1))).truncate (f i + 1) =
      (H.truncate (f i)).succ (H.oneType (f i) (f i)) := by
  have hlt : f i < f (i + 1) := hf (Nat.lt_succ_self i)
  have hstep : f i + 1 ≤ f (i + 1) := by omega
  exact H.enum_gap_succ hstep

end EnumNode
end ThreeUniformDiaries
