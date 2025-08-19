import Std.Do.Triple
import Std.Tactic.Do

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
  Vector.mk v.toArray v.size_toArray

-- LLM HELPER
/-- Hoare triple for pure computations -/
def hoare_triple_pure {α : Type} (P : Prop) (x : Id α) (Q : α → Prop) : Prop :=
  P → Q (Id.run x)

-- LLM HELPER
notation "⦃" P "⦄" x "⦃⇓" h " => " Q "⦄" => hoare_triple_pure P x (fun h => Q)

def problem_spec {α : Type} {n : Nat} (impl : DLPackObject α n → Option String → Option Bool → Id (Vector α n)) 
    (x : DLPackObject α n) (device : Option String) (copy : Option Bool) : Prop :=
  x.has_dlpack ∧ x.has_dlpack_device ∧ 
  (device.isNone ∨ device = some "cpu") →
  ∀ i : Fin n, (Id.run (impl x device copy)).get i = x.data.get i ∧
  (copy = some true → Id.run (impl x device copy) ≠ x.data) ∧
  (copy = some false → Id.run (impl x device copy) = x.data)

/-- Create a NumPy array from an object implementing the DLPack protocol -/
def from_dlpack {α : Type} {n : Nat} (x : DLPackObject α n) (_ : Option String := none) 
    (copy : Option Bool := none) : Id (Vector α n) :=
  match copy with
  | some true => x.data.copy
  | some false => x.data
  | none => x.data

-- LLM HELPER
lemma vector_copy_ne {α : Type} {n : Nat} (v : Vector α n) : v.copy ≠ v := by
  intro h_eq
  unfold Vector.copy at h_eq
  simp [Vector.mk] at h_eq

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
          exact vector_copy_ne x.data
        | false => simp at h_copy_true
    · intro h_copy_false
      cases copy with
      | none => simp at h_copy_false
      | some b =>
        cases b with
        | true => simp at h_copy_false
        | false => simp