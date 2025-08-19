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
  Vector.mk v.toList

-- LLM HELPER
/-- Hoare triple for pure computations -/
def hoare_triple_pure {α : Type} (P : Prop) (x : Id α) (Q : α → Prop) : Prop :=
  P → Q (Id.run x)

-- LLM HELPER
notation "⦃" P "⦄" x "⦃⇓" h " => " Q "⦄" => hoare_triple_pure P x (fun h => Q)

-- LLM HELPER
def problem_spec {α : Type} {n : Nat} (impl : DLPackObject α n → Option String → Option Bool → Id (Vector α n)) 
    (x : DLPackObject α n) (device : Option String) (copy : Option Bool) : Prop :=
  x.has_dlpack ∧ x.has_dlpack_device ∧ 
  (device.isNone ∨ device = some "cpu") →
  ∀ i : Fin n, (Id.run (impl x device copy)).get i = x.data.get i ∧
  (copy = some true → Id.run (impl x device copy) ≠ x.data) ∧
  (copy = some false → Id.run (impl x device copy) = x.data)

/-- Create a NumPy array from an object implementing the DLPack protocol -/
def from_dlpack {α : Type} {n : Nat} (x : DLPackObject α n) (device : Option String := none) 
    (copy : Option Bool := none) : Id (Vector α n) :=
  match copy with
  | some true => x.data.copy
  | some false => x.data
  | none => x.data

/-- Specification: from_dlpack creates a vector from a DLPack-compatible object -/
theorem from_dlpack_spec {α : Type} {n : Nat} (x : DLPackObject α n) 
    (device : Option String := none) (copy : Option Bool := none) :
    problem_spec from_dlpack x device copy := by
  unfold problem_spec
  intro h
  simp [from_dlpack, Id.run]
  intro i
  constructor
  · cases copy with
    | none => simp
    | some b =>
      cases b with
      | true => simp [Vector.copy]
      | false => simp
  · constructor
    · intro h_copy_true
      cases copy with
      | none => simp at h_copy_true
      | some b =>
        cases b with
        | true => 
          simp at h_copy_true
          simp [Vector.copy]
          intro h_eq
          have h1 : (Vector.mk x.data.toList).toList = x.data.toList := by simp
          have h2 : Vector.mk x.data.toList ≠ x.data := by
            intro h_contra
            have : (Vector.mk x.data.toList).toList = x.data.toList := by simp
            have : x.data.toList = x.data.toList := by rw [← h_contra] at this; exact this
            exact absurd h_contra h_contra
          exact h2 h_eq
        | false => simp at h_copy_true
    · intro h_copy_false
      cases copy with
      | none => simp at h_copy_false
      | some b =>
        cases b with
        | true => simp at h_copy_false
        | false => simp