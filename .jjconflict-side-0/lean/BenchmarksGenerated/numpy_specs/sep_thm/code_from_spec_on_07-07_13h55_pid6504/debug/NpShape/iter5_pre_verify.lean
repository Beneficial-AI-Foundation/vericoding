/-
# NumPy Shape Specification

Port of np_shape.dfy to Lean 4
-/

namespace DafnySpecs.NpShape

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := Vector (Vector α n) m

-- LLM HELPER
def Array3 (α : Type*) (l m n : Nat) : Type* := Vector (Vector (Vector α n) m) l

/-- Array type union for different dimensions -/
inductive arrays where
  | arrayOne (n : Nat) (arr1 : Vector Float n) : arrays
  | arrayTwo (m n : Nat) (arr2 : Matrix Float m n) : arrays
  | arrayThree (l m n : Nat) (arr3 : Array3 Float l m n) : arrays

-- LLM HELPER
def Vector.ofList (l : List α) : Vector α l.length := 
  ⟨l.toArray, by simp⟩

-- LLM HELPER
def get_shape_dim (a : arrays) : Nat :=
  match a with
  | arrays.arrayOne _ _ => 1
  | arrays.arrayTwo _ _ _ => 2
  | arrays.arrayThree _ _ _ _ => 3

/-- Get shape of multi-dimensional array -/
def shape'' (a : arrays) : Vector Int (get_shape_dim a) := 
  match a with
  | arrays.arrayOne n arr1 => Vector.ofList [Int.ofNat n]
  | arrays.arrayTwo m n arr2 => Vector.ofList [Int.ofNat m, Int.ofNat n]
  | arrays.arrayThree l m n arr3 => Vector.ofList [Int.ofNat l, Int.ofNat m, Int.ofNat n]

/-- Get shape of 2D array -/
def shape {m n : Nat} (a : Matrix Float m n) : Vector Int 2 := 
  Vector.ofList [Int.ofNat m, Int.ofNat n]

-- LLM HELPER
lemma vector_get_ofList {α : Type*} (l : List α) (i : Fin l.length) :
  (Vector.ofList l)[i] = l[i]! := by
  simp [Vector.ofList]

-- LLM HELPER
lemma vector_length_ofList {α : Type*} (l : List α) :
  (Vector.ofList l).toArray.size = l.length := by
  simp [Vector.ofList]

/-- Specification: Shape'' returns correct dimensions -/
theorem shape''_spec (a : arrays) :
  let ret := shape'' a
  match a with
  | arrays.arrayOne n arr1 => ret.toArray.size = 1 ∧ ret[0]! = Int.ofNat n
  | arrays.arrayTwo m n arr2 => ret.toArray.size = 2 ∧ ret[0]! = Int.ofNat m ∧ ret[1]! = Int.ofNat n
  | arrays.arrayThree l m n arr3 => ret.toArray.size = 3 ∧ ret[0]! = Int.ofNat l ∧ ret[1]! = Int.ofNat m ∧ ret[2]! = Int.ofNat n := by
  cases a with
  | arrayOne n arr1 => 
    simp [shape'', get_shape_dim, Vector.ofList]
    constructor
    · rfl
    · rfl
  | arrayTwo m n arr2 =>
    simp [shape'', get_shape_dim, Vector.ofList]
    constructor
    · rfl
    · constructor
      · rfl
      · rfl
  | arrayThree l m n arr3 =>
    simp [shape'', get_shape_dim, Vector.ofList]
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
  ret.toArray.size = 2 := by
  simp [shape, Vector.ofList]

/-- Specification: Shape returns correct dimensions -/
theorem shape_spec {m n : Nat} (a : Matrix Float m n) :
  let ret := shape a
  ret[0]! = Int.ofNat m ∧ ret[1]! = Int.ofNat n := by
  simp [shape, Vector.ofList]
  constructor
  · rfl
  · rfl

end DafnySpecs.NpShape