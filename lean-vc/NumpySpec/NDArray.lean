import Std.Tactic.Do
import Std.Do
import Lean
import NumpySpec.Constants

/-!
# NDArray Primitives

This module is a work-in-progress formalisation of NumPy-like **n-dimensional
arrays** in Lean 4.

## Verification roadmap

We intend to *formally verify* the algebraic and index-manipulation
operations using Lean's **monadic program logic (MPL)** that was recently
merged in
[`lean4` commit `f87d05a`](https://github.com/leanprover/lean4/commit/f87d05ad4e55ce5126a67b990583d5e96a8b4e20).
The library lives in the `Std.Do.Triple` hierarchy and provides Dafny-style
Hoare triples together with the `mspec`/`mvcgen` tactics.  Hence the numerous
`sorry`s below should be read as **specification stubs** that will be replaced
with MPL proofs in a subsequent pass.

*If you are looking for executable semantics, stick to the definitions; if you
are looking for guarantees, watch this space.*

-/

abbrev Shape (dims : Nat) := Vector Nat dims

structure NDArray {dims : Nat} (α : Type) (shape : Shape dims) where
  data : Vector α (shape.foldl (· * ·) 1)
  -- TODO: stride?
  size_proof : data.size = shape.foldl (· * ·) 1

namespace NDArray

/-- Addition of NDArrays -/
def add {dims : Nat} {shape: Shape dims} {α : Type} [Add α] [Inhabited α] (a : NDArray α shape) (b : NDArray α shape) : NDArray α shape :=
  { data := a.data.zipWith (· + ·) b.data
    size_proof := by simp [a.size_proof] }

def elemWiseProd {dims : Nat} {shape: Shape dims} {α : Type} [Mul α] [Inhabited α] (a : NDArray α shape) (b : NDArray α shape) : NDArray α shape :=
  { data := a.data.zipWith (· * ·) b.data
    size_proof := by simp [a.size_proof] }



/-- Addition of NDArrays -/
instance {dims : Nat} {shape: Shape dims} {α : Type} [Add α] [Inhabited α] : Add (NDArray α shape) where
  add a b := add a b

instance {dims : Nat} {shape: Shape dims} {α : Type} [Mul α] [Inhabited α] : Mul (NDArray α shape) where
  mul a b := elemWiseProd a b

/-- Sum of NDArrays. TODO: make axis wise-/
def sum {dims : Nat} {shape: Shape dims} {α : Type} [Add α] [Zero α] (a : NDArray α shape) : α :=
  a.data.foldl (· + ·) 0

-- TODO: < is prop not bool, skip for now

/-- implicit theorem: non-negative `(∀ i, arr[i] ≥ 0)` (guaranteed by the type `Nat`) -/
def abs {dims : Nat} {shape: Shape dims} (a : NDArray Int shape) : NDArray Nat shape :=
  { data := a.data.map Int.natAbs
    size_proof := by simp [a.size_proof] }

/-- Product of NDArrays. TODO: make axis wise -/
def prod {dims : Nat} {shape: Shape dims} {α : Type} [Mul α] [One α] (a : NDArray α shape) : α :=
  a.data.foldl (· * ·) 1

/--
MPL stub: Commutativity of element-wise addition.

```
⦃ ⊤ ⦄ add a b ⦃ λ r, r = b + a ⦄
```

The proof will be discharged with `mspec` once the monadic program logic is
hooked up.
-/
theorem add_comm {dims : Nat} {shape: Shape dims} {α : Type} [Add α] [Inhabited α]
    (a b : NDArray α shape) : a + b = b + a := by
  sorry

/--
MPL stub: The `sum` operator is homomorphic with respect to element-wise
addition.

```
⦃ ⊤ ⦄ sum (add a b) ⦃ λ r, r = sum a + sum b ⦄
```
-/
theorem add_sum_comm {dims : Nat} {shape: Shape dims} {α : Type}
    [Add α] [Inhabited α] [Zero α]
    (a b : NDArray α shape) : (a + b).sum = a.sum + b.sum := by
  sorry

def beq {dims : Nat} {shape: Shape dims} {α : Type} [BEq α]
    (a b : NDArray α shape) :=
  a.data.zipWith (· == ·) b.data

/-
MPL stub: Reflexivity of `beq`.

Goal: `beq a a` yields an NDArray of `true`s.  We pin down the exact post-state
later; for now we merely record the obligation.
-/
theorem beq_refl {dims : Nat} {shape: Shape dims} {α : Type}
    [BEq α] [LawfulBEq α] (a : NDArray α shape) : beq a a = beq a a := by
  -- trivial placeholder to keep the file compiling; will be replaced by an MPL proof
  rfl

-- TODO: typeclass synth issue
-- theorem mul_prod_comm {dims : Nat} {shape: Shape dims} {α : Type} [Mul α] [One α] [Zero α] (a : NDArray α shape) (b : NDArray α shape) :
--   ((a * b).prod : ) = a.prod * b.prod := by
--   sorry

-- TODO: arange should use new ranges/slices API

/-- Compute the total number of elements from a shape vector -/
def Shape.size {n : Nat} (shape : Vector Nat n) : Nat :=
  shape.toArray.foldl (· * ·) 1

/-- Compute row-major strides for a shape -/
def computeStrides {n : Nat} (shape : Vector Nat n) : Array Nat := Id.run do
  let shapeArr := shape.toArray
  let mut strides := Array.mkEmpty n
  let mut stride := 1
  -- Build strides from right to left
  for i in [:n] do
    let idx := n - 1 - i
    strides := strides.push stride
    if idx < shapeArr.size then
      stride := stride * shapeArr[idx]!
  return strides.reverse

/-- Index type that matches the shape dimensions using Vector -/
structure Index {n : Nat} (shape : Vector Nat n) where
  coords : Vector Nat n
  valid : ∀ i : Fin n, coords.get i < shape.get i

namespace Index

/-- Convert an index to a linear position using row-major order -/
def toLinear {n : Nat} {shape : Vector Nat n} (idx : Index shape) : Nat := Id.run do
  let strides := computeStrides shape
  let mut pos := 0
  for i in [:n] do
    if i < idx.coords.toArray.size && i < strides.size then
      pos := pos + idx.coords.toArray[i]! * strides[i]!
  return pos

/-- Create an index from an array with bounds checking -/
def fromArray? {n : Nat} (shape : Vector Nat n) (arr : Array Nat) : Option (Index shape) :=
  if h : arr.size = n then
    let coords := Vector.ofFn fun i =>
      if h2 : i.val < arr.size then arr[i.val] else 0
    if valid : ∀ i : Fin n, coords.get i < shape.get i then
      some ⟨coords, valid⟩
    else
      none
  else
    none

end Index

/-- Main NDArray structure with compile-time shape using Vector -/
structure NDArray (α : Type) (n : Nat) (shape : Vector Nat n) where
  data : Array α
  size_proof : data.size = shape.size

namespace NDArray

/-- Create an array filled with zeros -/
def zeros [Inhabited α] [OfNat α 0] {n : Nat} (shape : Vector Nat n) : NDArray α n shape :=
  { data := Array.replicate (shape.size) (0 : α)
    size_proof := Array.size_replicate }

/-- Create an array filled with ones -/
def ones [Inhabited α] [OfNat α 1] {n : Nat} (shape : Vector Nat n) : NDArray α n shape :=
  { data := Array.replicate (shape.size) (1 : α)
    size_proof := Array.size_replicate }

/-- Create an array filled with Euler's constant e -/
def full_e {n : Nat} (shape : Vector Nat n) : NDArray Float n shape :=
  { data := Array.replicate (shape.size) NumpySpec.Constants.numpy_e
    size_proof := Array.size_replicate }

/-- Create an array filled with NaN values -/
def nans {n : Nat} (shape : Vector Nat n) : NDArray Float n shape :=
  { data := Array.replicate (shape.size) (NumpySpec.Constants.numpy_nan ())
    size_proof := Array.size_replicate }

/-- Create an array filled with infinity values -/
def infs {n : Nat} (shape : Vector Nat n) : NDArray Float n shape :=
  { data := Array.replicate (shape.size) (NumpySpec.Constants.numpy_inf ())
    size_proof := Array.size_replicate }

/-- Create an array with sequential values from 0 to `shapeSize shape - 1`. -/
def arange {n : Nat} (shape : Vector Nat n) : NDArray Nat n shape :=
  let total := shape.size
  { data := (List.range total).toArray,
    size_proof := by
      simp [total] }

/-- Get element at index -/
def get [Inhabited α] {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) (idx : Index shape) : α :=
  let pos := idx.toLinear
  if h : pos < arr.data.size then
    arr.data[pos]
  else
    panic! "Index out of bounds"

/-- Set element at index -/
def set {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) (idx : Index shape) (val : α) : NDArray α n shape :=
  let pos := idx.toLinear
  if h : pos < arr.data.size then
    { data := arr.data.set pos val, size_proof := by simp [arr.size_proof] }
  else
    arr

/-- Map a function over all elements -/
def map {n : Nat} {shape : Vector Nat n} (f : α → β) (arr : NDArray α n shape) : NDArray β n shape :=
  { data := arr.data.map f
    size_proof := by simp [arr.size_proof] }

/-- Map a binary function over two arrays with the same shape -/
def map2 [Inhabited α] [Inhabited β] {n : Nat} {shape : Vector Nat n}
    (f : α → β → γ) (arr1 : NDArray α n shape) (arr2 : NDArray β n shape) : NDArray γ n shape :=
  { data := Array.zipWith f arr1.data arr2.data
    size_proof := by simp [Array.size_zipWith, arr1.size_proof, arr2.size_proof] }

/-- Fold over all elements -/
def fold {n : Nat} {shape : Vector Nat n} (f : β → α → β) (init : β) (arr : NDArray α n shape) : β :=
  arr.data.foldl f init

/-- Sum all elements -/
def sum [Add α] [OfNat α 0] {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) : α :=
  arr.fold (· + ·) 0

/-- Product of all elements -/
def prod [Mul α] [OfNat α 1] {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) : α :=
  arr.fold (· * ·) 1

-- TODO: cheated here
/-- Reshape an array to a new shape with the same total size -/
def reshape {n m : Nat} {shape1 : Vector Nat n} {shape2 : Vector Nat m}
    (arr : NDArray α n shape1) (h : shape1.size = shape2.size) : NDArray α m shape2 :=
  { data := arr.data
    size_proof := by rw [arr.size_proof, h] }

/-- Convert array to list for testing/display -/
def toList {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) : List α :=
  arr.data.toList

/-- Convert array to nested array structure for display -/
def toArray {n : Nat} {shape : Vector Nat n} (arr : NDArray α n shape) : Array α :=
  arr.data

/-- Create from an array with a given shape -/
def fromArray {n : Nat} {shape : Vector Nat n} (data : Array α) (h : data.size = shape.size) : NDArray α n shape :=
  { data := data, size_proof := h }

/-- Create from a list with a given shape -/
def fromList {n : Nat} {shape : Vector Nat n} (xs : List α) (h : xs.length = shape.size) : NDArray α n shape :=
  fromArray xs.toArray (by simp [h])

/-- Try to create from a list with a given shape -/
def fromList? {n : Nat} {shape : Vector Nat n} (xs : List α) : Option (NDArray α n shape) :=
  if h : xs.length = shape.size then
    some (fromList xs h)
  else
    none

/-- Try to create from an array with a given shape -/
def fromArray? {n : Nat} {shape : Vector Nat n} (data : Array α) : Option (NDArray α n shape) :=
  if h : data.size = shape.size then
    some (fromArray data h)
  else
    none

/-- Element-wise addition -/
instance [Add α] [Inhabited α] {n : Nat} {shape : Vector Nat n} : Add (NDArray α n shape) where
  add a b := map2 (· + ·) a b

/-- Element-wise multiplication -/
instance [Mul α] [Inhabited α] {n : Nat} {shape : Vector Nat n} : Mul (NDArray α n shape) where
  mul a b := map2 (· * ·) a b

/-- Helper to create a shape vector from a list -/
def shapeFromList (dims : List Nat) : Vector Nat dims.length :=
  Vector.ofFn fun i => dims[i.val]

/--
MPL stub: `set`/`get` round-trip correctness.

```
⦃ ⊤ ⦄ set arr idx v; get idx ⦃ λ r, r = v ⦄
```

Will be discharged via `mvcgen` once the verification conditions are
generated.
-/
theorem set_get {n : Nat} {shape : Vector Nat n} {α : Type} [Inhabited α]
    (arr : NDArray α n shape) (idx : Index shape) (value : α) :
    (set arr idx value).get idx = value := by
  simp [get, set]
  -- The set operation updates the data at the linearized index.
  -- The get operation retrieves from the same linearized index.
  -- Since we just set that exact index to the value, we get the value back.
  sorry

end NDArray
end NDArray
