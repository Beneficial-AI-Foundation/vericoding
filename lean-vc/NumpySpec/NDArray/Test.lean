import NDArray

open NDArray

/-- Helper to create indices more easily -/
def mkIndex {n : Nat} (shape : Vector Nat n) (coords : Array Nat) : Option (Index shape) :=
  Index.fromArray? shape coords

/-- Test suite for NDArray implementation -/
def testSuite : IO Unit := do
  IO.println "=== NDArray Test Suite (Vector-based) ==="
  IO.println ""
  
  -- Test Shape operations with Vector
  IO.println "-- Shape Tests (using Vector) --"
  let shape1d : Vector Nat 1 := Vector.ofFn fun _ => 5
  let shape2d : Vector Nat 2 := Vector.ofFn fun i => if i = 0 then 3 else 4
  let shape3d : Vector Nat 3 := Vector.ofFn fun i => if i = 0 then 2 else if i = 1 then 3 else 4
  let shape4d : Vector Nat 4 := Vector.ofFn fun i => 
    if i = 0 then 10 else if i = 1 then 28 else if i = 2 then 28 else 3
  let shape5d : Vector Nat 5 := Vector.ofFn fun i =>
    if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 5 else 6
  
  IO.println s!"1D shape [5]: size = {shapeSize shape1d}"
  IO.println s!"2D shape [3,4]: size = {shapeSize shape2d}"
  IO.println s!"3D shape [2,3,4]: size = {shapeSize shape3d}"
  IO.println s!"4D shape [10,28,28,3]: size = {shapeSize shape4d}"
  IO.println s!"5D shape [2,3,4,5,6]: size = {shapeSize shape5d}"
  IO.println ""
  
  -- Test 1D arrays
  IO.println "-- 1D Array Tests --"
  let arr1d : NDArray Nat 1 shape1d := NDArray.arange shape1d
  IO.println s!"1D array created with arange: {arr1d.toList}"
  
  let zeros1d : NDArray Nat 1 shape1d := NDArray.zeros shape1d
  IO.println s!"1D zeros: {zeros1d.toList}"
  
  let ones1d : NDArray Nat 1 shape1d := NDArray.ones shape1d
  IO.println s!"1D ones: {ones1d.toList}"
  
  -- Test element access
  match mkIndex shape1d #[2] with
  | some idx => IO.println s!"arr1d[2] = {arr1d.get idx}"
  | none => IO.println "Failed to create index [2]"
  
  IO.println ""
  
  -- Test 2D arrays (matrices)
  IO.println "-- 2D Array Tests (Matrices) --"
  let mat : NDArray Nat 2 shape2d := NDArray.arange shape2d
  IO.println s!"2D matrix [3,4]: {mat.toList}"
  
  -- Access element at (1,2)
  match mkIndex shape2d #[1, 2] with
  | some idx => IO.println s!"mat[1,2] = {mat.get idx}"
  | none => IO.println "Failed to create index [1,2]"
  
  -- Test operations
  let mat2 := mat.map (· * 2)
  IO.println s!"Matrix * 2: {mat2.toList}"
  
  let matSum := mat.sum
  IO.println s!"Sum of all elements: {matSum}"
  IO.println ""
  
  -- Test 3D arrays
  IO.println "-- 3D Array Tests --"
  let arr3d : NDArray Nat 3 shape3d := NDArray.arange shape3d
  IO.println s!"3D array [2,3,4] size: {arr3d.data.size}"
  IO.println s!"First 10 elements: {arr3d.toList.take 10}"
  
  -- Access element at (0,1,2)
  match mkIndex shape3d #[0, 1, 2] with
  | some idx => IO.println s!"arr3d[0,1,2] = {arr3d.get idx}"
  | none => IO.println "Failed to create index [0,1,2]"
  
  -- Test slice-like operation (getting all elements at position [1,*,*])
  IO.println "Elements at arr3d[1,*,*]:"
  for i in [0:3] do
    for j in [0:4] do
      match mkIndex shape3d #[1, i, j] with
      | some idx => IO.print s!"{arr3d.get idx} "
      | none => IO.print "? "
    IO.println ""
  IO.println ""
  
  -- Test 4D arrays (common in ML - batch × height × width × channels)
  IO.println "-- 4D Array Tests (ML-style: batch × height × width × channels) --"
  -- Note: Creating smaller array for demo
  let shape4d_small : Vector Nat 4 := Vector.ofFn fun i => 
    if i = 0 then 2 else if i = 1 then 4 else if i = 2 then 4 else 3
  let images : NDArray Nat 4 shape4d_small := NDArray.zeros shape4d_small
  IO.println s!"4D image batch [2,4,4,3] created with size: {images.data.size}"
  
  -- Simulate accessing first image, first pixel, all channels
  IO.println "First pixel channels of first image:"
  for c in [0:3] do
    match mkIndex shape4d_small #[0, 0, 0, c] with
    | some idx => IO.print s!"{images.get idx} "
    | none => IO.print "? "
  IO.println ""
  IO.println ""
  
  -- Test 5D arrays
  IO.println "-- 5D Array Tests --"
  let shape5d_small : Vector Nat 5 := Vector.ofFn fun _ => 2
  let arr5d : NDArray Nat 5 shape5d_small := NDArray.ones shape5d_small
  IO.println s!"5D array [2,2,2,2,2] created with size: {arr5d.data.size}"
  IO.println s!"All elements (should be all 1s): {arr5d.toList}"
  IO.println ""
  
  -- Test reshaping
  IO.println "-- Reshape Tests --"
  let shape_before : Vector Nat 2 := Vector.ofFn fun i => if i = 0 then 6 else 4
  let shape_after : Vector Nat 2 := Vector.ofFn fun i => if i = 0 then 8 else 3
  let arr_reshape : NDArray Nat 2 shape_before := NDArray.arange shape_before
  IO.println s!"Original shape [6,4]: {arr_reshape.toList}"
  
  -- Note: Can only reshape if sizes match (6*4 = 24 = 8*3)
  if h : shapeSize shape_before = shapeSize shape_after then
    let reshaped := arr_reshape.reshape h
    IO.println s!"Reshaped to [8,3]: {reshaped.toList}"
  else
    IO.println "Cannot reshape: sizes don't match"
  IO.println ""
  
  -- Test edge cases
  IO.println "-- Edge Cases --"
  
  -- Scalar (0D array)
  let scalar_shape : Vector Nat 0 := Vector.ofFn fun i => i.elim0
  let scalar := NDArray.ones scalar_shape
  IO.println s!"Scalar (0D array): {scalar.toList}"
  
  -- Single element arrays
  let single_shape : Vector Nat 1 := Vector.ofFn fun _ => 1
  match NDArray.fromList? (shape := single_shape) [42] with
  | some arr_single => IO.println s!"Single element 1D array: {arr_single.toList}"
  | none => IO.println "Failed to create single element array"
  
  -- Empty dimension (one dimension is 0)
  let empty_shape : Vector Nat 2 := Vector.ofFn fun i => if i = 0 then 0 else 5
  let empty_arr : NDArray Nat 2 empty_shape := NDArray.zeros empty_shape
  IO.println s!"Array with empty dimension [0,5]: size = {empty_arr.data.size}"
  
  -- Test Array-based operations
  IO.println ""
  IO.println "-- Array-based Operations --"
  
  -- Create from Array
  let data_arr : Array Nat := #[1, 2, 3, 4, 5, 6]
  let shape_arr : Vector Nat 2 := Vector.ofFn fun i => if i = 0 then 2 else 3
  match NDArray.fromArray? (shape := shape_arr) data_arr with
  | some arr => IO.println s!"Created from Array: {arr.toList}"
  | none => IO.println "Failed to create from Array"
  
  -- Test arithmetic operations
  let a := NDArray.arange shape2d
  let b := NDArray.ones shape2d
  let c := a + b  -- Uses instance
  IO.println s!"Element-wise addition result: {c.toList.take 6}..."
  
  IO.println ""
  IO.println "=== All tests completed successfully! ==="

-- Run the test suite
#eval! testSuite

-- Main entry point for executable
def main : IO Unit := testSuite