import ThreeUniformDiaries.TypeTrees

/-!
# Canonical maps between the three type trees

This is the algebraic content of the manuscript's canonical-map lemma.
A canonical map has one strictly increasing level map and compatible maps on
enumerations, 1-types, and auxiliary types.  Compatibility says exactly that
restriction, 1-type formation, and auxiliary-type formation commute with the
map.

The repaired manuscript needs these maps to compose; that statement is
proved here rather than hidden in the final Ramsey argument.
-/

namespace ThreeUniformDiaries

/-- The synchronized canonical map on the enumeration, 1-type, and aux-type
trees. -/
structure CanonicalMap where
  level : Nat → Nat
  strictMono : StrictMono level

  mapAux : (n : Nat) → AuxNode n → AuxNode (level n)
  mapOne : (n : Nat) → OneNode n → OneNode (level n)
  mapEnum : (n : Nat) → EnumNode n → EnumNode (level n)

  enum_triple_compat :
    ∀ {N i j k : Nat} (H : EnumNode N),
      i < j → j < k → k < N →
      (mapEnum N H).triple (level i) (level j) (level k) =
        H.triple i j k

  truncate_compat :
    ∀ {N l : Nat} (H : EnumNode N), l ≤ N →
      mapEnum l (H.truncate l) =
        (mapEnum N H).truncate (level l)

  oneType_compat :
    ∀ {N l v : Nat} (H : EnumNode N),
      l ≤ v → v < N →
      mapOne l (H.oneType l v) =
        (mapEnum N H).oneType (level l) (level v)

  auxType_compat :
    ∀ {N l u v : Nat} (H : EnumNode N),
      l ≤ u → u < v → v < N →
      mapAux l (H.auxType l u v) =
        (mapEnum N H).auxType (level l) (level u) (level v)

namespace CanonicalMap

/-- The identity canonical map. -/
def id : CanonicalMap where
  level := fun n => n
  strictMono := strictMono_id
  mapAux := fun _ a => a
  mapOne := fun _ a => a
  mapEnum := fun _ a => a
  enum_triple_compat := by
    intro N i j k H hij hjk hkN
    rfl
  truncate_compat := by
    intro N l H hl
    rfl
  oneType_compat := by
    intro N l v H hlv hvN
    rfl
  auxType_compat := by
    intro N l u v H hlu huv hvN
    rfl

/-- Composition of synchronized canonical maps. -/
def comp (G F : CanonicalMap) : CanonicalMap where
  level := fun n => G.level (F.level n)
  strictMono := G.strictMono.comp F.strictMono
  mapAux := fun n a => G.mapAux (F.level n) (F.mapAux n a)
  mapOne := fun n a => G.mapOne (F.level n) (F.mapOne n a)
  mapEnum := fun n a => G.mapEnum (F.level n) (F.mapEnum n a)
  enum_triple_compat := by
    intro N i j k H hij hjk hkN
    rw [G.enum_triple_compat (F.mapEnum N H)
      (F.strictMono hij) (F.strictMono hjk) (F.strictMono hkN)]
    exact F.enum_triple_compat H hij hjk hkN
  truncate_compat := by
    intro N l H hl
    rw [F.truncate_compat H hl]
    rw [G.truncate_compat (F.mapEnum N H)
      (F.strictMono.monotone hl)]
  oneType_compat := by
    intro N l v H hlv hvN
    rw [F.oneType_compat H hlv hvN]
    rw [G.oneType_compat (F.mapEnum N H)
      (F.strictMono.monotone hlv) (F.strictMono hvN)]
  auxType_compat := by
    intro N l u v H hlu huv hvN
    rw [F.auxType_compat H hlu huv hvN]
    rw [G.auxType_compat (F.mapEnum N H)
      (F.strictMono.monotone hlu) (F.strictMono huv)
      (F.strictMono hvN)]

@[simp] theorem id_level (n : Nat) :
    id.level n = n := rfl

@[simp] theorem comp_level (G F : CanonicalMap) (n : Nat) :
    (comp G F).level n = G.level (F.level n) := rfl

@[simp] theorem id_mapAux {n : Nat} (a : AuxNode n) :
    id.mapAux n a = a := rfl

@[simp] theorem id_mapOne {n : Nat} (a : OneNode n) :
    id.mapOne n a = a := rfl

@[simp] theorem id_mapEnum {n : Nat} (a : EnumNode n) :
    id.mapEnum n a = a := rfl

@[simp] theorem comp_mapAux (G F : CanonicalMap)
    {n : Nat} (a : AuxNode n) :
    (comp G F).mapAux n a =
      G.mapAux (F.level n) (F.mapAux n a) := rfl

@[simp] theorem comp_mapOne (G F : CanonicalMap)
    {n : Nat} (a : OneNode n) :
    (comp G F).mapOne n a =
      G.mapOne (F.level n) (F.mapOne n a) := rfl

@[simp] theorem comp_mapEnum (G F : CanonicalMap)
    {n : Nat} (a : EnumNode n) :
    (comp G F).mapEnum n a =
      G.mapEnum (F.level n) (F.mapEnum n a) := rfl

/-- Canonical composition is associative on every component. -/
theorem comp_assoc (H G F : CanonicalMap) :
    comp (comp H G) F = comp H (comp G F) := by
  cases F
  cases G
  cases H
  rfl

@[simp] theorem comp_id (F : CanonicalMap) :
    comp F id = F := by
  cases F
  rfl

@[simp] theorem id_comp (F : CanonicalMap) :
    comp id F = F := by
  cases F
  rfl

end CanonicalMap
end ThreeUniformDiaries
