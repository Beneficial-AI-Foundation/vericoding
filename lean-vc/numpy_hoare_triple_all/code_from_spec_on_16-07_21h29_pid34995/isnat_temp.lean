import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- A datetime64 type placeholder representing either a valid datetime or NaT (Not a Time) -/
inductive DateTime64 where
  /-- Valid datetime represented as float (seconds since epoch) -/
  | valid : Float → DateTime64
  /-- NaT (Not a Time) - the datetime equivalent of NaN -/
  | nat : DateTime64

-- LLM HELPER
/-- Helper function to check if a single DateTime64 value is NaT -/
def isnat_single (dt : DateTime64) : Bool :=
  match dt with
  | DateTime64.nat => true
  | DateTime64.valid _ => false

/-- Test element-wise for NaT (not a time) and return result as a boolean array.
    
    This function checks each element of a datetime64 array to determine if it
    represents NaT (Not a Time), which is the datetime equivalent of NaN.
    
    Returns true for NaT values and false for all valid datetime values.
    The function is the datetime analog of isnan for floating point values.
-/
def isnat {n : Nat} (x : Vector DateTime64 n) : Id (Vector Bool n) :=
  return x.map isnat_single

-- LLM HELPER
lemma isnat_single_spec (dt : DateTime64) :
  isnat_single dt = match dt with
  | DateTime64.nat => true
  | DateTime64.valid _ => false := by
  cases dt <;> simp [isnat_single]

-- LLM HELPER
lemma vector_map_get {α β : Type} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
  (v.map f).get i = f (v.get i) := by
  simp [Vector.map, Vector.get]

/-- Specification: isnat returns true for NaT values and false otherwise.
    The function correctly identifies NaT values in datetime64 arrays.
    
    Mathematical properties:
    1. NaT detection: result[i] = true iff x[i] is NaT
    2. Valid datetime detection: result[i] = false iff x[i] is a valid datetime
    3. Result preserves shape: output vector has same length as input
    4. Exhaustive coverage: every element is either NaT or a valid datetime
    
    This is the datetime analog of isnan for floating point NaN values.
-/
theorem isnat_spec {n : Nat} (x : Vector DateTime64 n) :
    ⦃⌜True⌝⦄
    isnat x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = match x.get i with
                                                | DateTime64.nat => true
                                                | DateTime64.valid _ => false) ∧
                 (∀ i : Fin n, result.get i = true ↔ x.get i = DateTime64.nat) ∧
                 (∀ i : Fin n, result.get i = false ↔ ∃ t : Float, x.get i = DateTime64.valid t)⌝⦄ := by
  simp [isnat]
  constructor
  · intro i
    rw [vector_map_get, isnat_single_spec]
  constructor
  · intro i
    rw [vector_map_get, isnat_single_spec]
    cases h : x.get i with
    | nat => simp
    | valid t => simp
  · intro i
    rw [vector_map_get, isnat_single_spec]
    cases h : x.get i with
    | nat => simp
    | valid t => simp; exact ⟨t, rfl⟩