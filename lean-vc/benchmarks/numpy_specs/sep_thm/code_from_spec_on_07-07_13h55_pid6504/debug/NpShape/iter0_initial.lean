/-
# NumPy Shape Specification

Port of np_shape.dfy to Lean 4
-/

namespace DafnySpecs.NpShape

/-- Array type union for different dimensions -/
inductive arrays where
  | arrayOne (arr1 : Vector Float n) : arrays
  | arrayTwo (arr2 : Matrix Float m n) : arrays
  | arrayThree (arr3 : Array3 Float l m n) : arrays

-- LLM HELPER
def Vector.ofList (l : List α) : Vector α l.length := 
  ⟨l, rfl⟩

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := Vector (Vector α n) m

-- LLM HELPER
def Array3 (α : Type*) (l m n : Nat) : Type* := Vector (Vector (Vector α n) m) l

/-- Get shape of multi-dimensional array -/
def shape'' (a : arrays) : Vector Int (match a with | arrays.arrayOne _ => 1 | arrays.arrayTwo _ _ => 2 | arrays.arrayThree _ _ _ => 3) := 
  match a with
  | arrays.arrayOne arr1 => Vector.ofList [arr1.toList.length]
  | arrays.arrayTwo arr2 => Vector.ofList [arr2.toList.length, if arr2.toList.length > 0 then arr2[0]!.toList.length else 0]
  | arrays.arrayThree arr3 => Vector.ofList [arr3.toList.length, 
    if arr3.toList.length > 0 then arr3[0]!.toList.length else 0,
    if arr3.toList.length > 0 ∧ arr3[0]!.toList.length > 0 then arr3[0]![0]!.toList.length else 0]

/-- Get shape of 2D array -/
def shape {m n : Nat} (a : Matrix Float m n) : Vector Int 2 := 
  Vector.ofList [m, n]

-- LLM HELPER
lemma vector_get_ofList {α : Type*} (l : List α) (i : Fin l.length) :
  (Vector.ofList l)[i] = l[i] := by
  rfl

-- LLM HELPER
lemma vector_length_ofList {α : Type*} (l : List α) :
  (Vector.ofList l).toList.length = l.length := by
  rfl

/-- Specification: Shape'' returns correct dimensions -/
theorem shape''_spec (a : arrays) :
  let ret := shape'' a
  match a with
  | arrays.arrayOne arr1 => ret.toList.length = 1 ∧ ret[0]! = arr1.toList.length
  | arrays.arrayTwo arr2 => ret.toList.length = 2 ∧ ret[0]! = arr2.toList.length ∧ ret[1]! = (if arr2.toList.length > 0 then arr2[0]!.toList.length else 0)
  | arrays.arrayThree arr3 => ret.toList.length = 3 ∧ ret[0]! = arr3.toList.length ∧ ret[1]! = (if arr3.toList.length > 0 then arr3[0]!.toList.length else 0) ∧ ret[2]! = (if arr3.toList.length > 0 ∧ arr3[0]!.toList.length > 0 then arr3[0]![0]!.toList.length else 0) := by
  cases a with
  | arrayOne arr1 => 
    simp [shape'']
    constructor
    · rfl
    · rfl
  | arrayTwo arr2 =>
    simp [shape'']
    constructor
    · rfl
    · constructor
      · rfl
      · rfl
  | arrayThree arr3 =>
    simp [shape'']
    constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · rfl

/-- Specification: Shape returns correct length -/
theorem shape_length {m n : Nat} (a : Matrix Float m n) :
  let ret := shape a
  ret.toList.length = 2 := by
  simp [shape]
  rfl

/-- Specification: Shape returns correct dimensions -/
theorem shape_spec {m n : Nat} (a : Matrix Float m n) :
  let ret := shape a
  ret[0]! = m ∧ ret[1]! = n := by
  simp [shape]
  constructor
  · rfl
  · rfl

end DafnySpecs.NpShape