import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.from_dlpack",
  "category": "From existing data",
  "description": "Create a NumPy array from an object implementing the __dlpack__ protocol",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.from_dlpack.html",
  "doc": "\nCreate a NumPy array from an object implementing the __dlpack__ protocol.\n\nParameters\n----------\nx : object\n    A Python object that implements the __dlpack__ and __dlpack_device__ methods.\ndevice : device, optional\n    Device on which to place the created array. Must be \"cpu\" if specified.\ncopy : bool, optional\n    If True, the array is copied. If False, the array is not copied. \n    If None (default), the array is only copied if necessary.\n\nReturns\n-------\nout : ndarray\n    Array created from the input object.\n\nNotes\n-----\nThis function allows for interoperability with other libraries that support the DLPack protocol.\n",
  "code": "def from_dlpack(x, /, *, device=None, copy=None):\n    \"\"\"\n    Create a NumPy array from an object implementing the \`\`__dlpack__\`\`\n    protocol. Generally, the returned NumPy array is a read-only view\n    of the input object. See [1]_ and [2]_ for more details.\n    \"\"\"\n    if hasattr(x, '__dlpack_device__') and hasattr(x, '__dlpack__'):\n        return _from_dlpack(x.__dlpack__(stream=None, \n                                       max_version=(1, 0),\n                                       dl_device=device,\n                                       copy=copy))\n    else:\n        raise TypeError(f\"The input must implement the DLPack protocol. \"\n                       f\"Got {type(x)}.\")",
  "signature": "numpy.from_dlpack(x, /, *, device=None, copy=None)"
}
-/

open Std.Do

/-- Abstract type representing a DLPack-compatible object -/
structure DLPackObject (α : Type) (n : Nat) where
  /-- The underlying data vector -/
  data : Vector α n
  /-- Whether the object has __dlpack__ method -/
  has_dlpack : Bool
  /-- Whether the object has __dlpack_device__ method -/
  has_dlpack_device : Bool
  /-- The device on which the object resides -/
  device : String
  deriving Repr

-- LLM HELPER
/-- Create a copy of a vector -/
def Vector.copy {α : Type} {n : Nat} (v : Vector α n) : Vector α n :=
  ⟨v.toArray.toList.toArray, by simp [Array.size_toArray]; rfl⟩

-- LLM HELPER
/-- Specification: from_dlpack creates a vector from a DLPack-compatible object -/
def problem_spec {α : Type} {n : Nat} (from_dlpack : DLPackObject α n → Option String → Option Bool → Vector α n) (x : DLPackObject α n) 
    (device : Option String := none) (copy : Option Bool := none) : Prop :=
    (x.has_dlpack = true ∧ x.has_dlpack_device = true ∧ 
      (device = none ∨ device = some "cpu")) →
    let result := from_dlpack x device copy
    (∀ i : Fin n, result.get i = x.data.get i) ∧
    (copy = some true → result ≠ x.data) ∧
    (copy = some false → result = x.data)

/-- Create a NumPy array from an object implementing the DLPack protocol -/
def from_dlpack {α : Type} {n : Nat} (x : DLPackObject α n) (device : Option String := none) 
    (copy : Option Bool := none) : Vector α n :=
  match copy with
  | some true => x.data.copy
  | some false => x.data
  | none => x.data

theorem correctness {α : Type} {n : Nat} (x : DLPackObject α n) 
    (device : Option String := none) (copy : Option Bool := none) :
    problem_spec from_dlpack x device copy := by
  intro h
  simp [from_dlpack]
  cases' copy with copy
  · simp
    constructor
    · intro i
      rfl
    · constructor <;> intro h_contra <;> contradiction
  · cases' copy with
    | true =>
      simp [Vector.copy]
      constructor
      · intro i
        simp [Vector.get, Vector.copy]
      · constructor
        · intro
          simp [Ne, Vector.copy]
          intro h_eq
          have : x.data.toArray.toList.toArray = x.data.toArray := by rw [h_eq]
          simp at this
        · intro h_contra
          contradiction
    | false =>
      simp
      constructor
      · intro i
        rfl
      · constructor
        · intro h_contra
          contradiction
        · intro
          rfl