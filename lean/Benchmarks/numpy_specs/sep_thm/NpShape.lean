/-
# NumPy Shape Specification

Port of np_shape.dfy to Lean 4
-/

import Benchmarks.MatrixDef

namespace DafnySpecs.NpShape

/-- Array type union for different dimensions -/
inductive arrays where
  | arrayOne (arr1 : Vector Float n) : arrays
  | arrayTwo (arr2 : Matrix m n Float) : arrays
  | arrayThree (arr3 : Array3 l m n Float) : arrays

/-- Get shape of multi-dimensional array -/
def shape'' (a : arrays) : Vector Int (match a with | arrays.arrayOne _ => 1 | arrays.arrayTwo _ _ => 2 | arrays.arrayThree _ _ _ => 3) := sorry

/-- Get shape of 2D array -/
def shape {m n : Nat} (a : Matrix m n Float) : Vector Int 2 := sorry

/-- Specification: Shape'' returns correct dimensions -/
theorem shape''_spec (a : arrays) :
  let ret := shape'' a
  match a with
  | arrays.arrayOne arr1 => ret.toList.length = 1 ∧ ret[0]! = arr1.toList.length
  | arrays.arrayTwo arr2 => ret.toList.length = 2 ∧ ret[0]! = arr2.toList.length ∧ ret[1]! = (if arr2.toList.length > 0 then arr2[0]!.toList.length else 0)
  | arrays.arrayThree arr3 => ret.toList.length = 3 ∧ ret[0]! = arr3.toList.length ∧ ret[1]! = (if arr3.toList.length > 0 then arr3[0]!.toList.length else 0) ∧ ret[2]! = (if arr3.toList.length > 0 ∧ arr3[0]!.toList.length > 0 then arr3[0]![0]!.toList.length else 0) := sorry

/-- Specification: Shape returns correct length -/
theorem shape_length {m n : Nat} (a : Matrix m n Float) :
  let ret := shape a
  ret.toList.length = 2 := sorry

/-- Specification: Shape returns correct dimensions -/
theorem shape_spec {m n : Nat} (a : Matrix m n Float) :
  let ret := shape a
  ret[0]! = m ∧ ret[1]! = n := sorry

end DafnySpecs.NpShape
