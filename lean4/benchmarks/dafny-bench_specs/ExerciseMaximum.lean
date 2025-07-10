import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Exercise: Maximum Element in Array

This module ports the Dafny specification for finding the maximum element 
in an array and its index.

The specification includes several variants:
- `mmaximum1`: Left-to-right scan returning the first maximum index
- `mmaximum2`: Right-to-left scan returning the last maximum index
- `mfirstMaximum`: Returns the first occurrence of the maximum
- `mlastMaximum`: Returns the last occurrence of the maximum
- `mmaxvalue1`: Returns the maximum value (left-to-right)
- `mmaxvalue2`: Returns the maximum value (right-to-left)
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseMaximum

/-- Implementation placeholder for mmaximum1 -/
def mmaximum1 (v : Array Int) : Id Nat := sorry

/-- Hoare triple for mmaximum1 (left-to-right, returns first) -/
theorem mmaximum1_spec (v : Array Int) (h : v.size > 0) :
    ⦃⌜v.size > 0⌝⦄ 
    mmaximum1 v
    ⦃⇓i => ⌜0 ≤ i ∧ i < v.size ∧ ∀ k, 0 ≤ k ∧ k < v.size → v[i]! ≥ v[k]!⌝⦄ := by
  sorry

/-- Implementation placeholder for mmaximum2 -/
def mmaximum2 (v : Array Int) : Id Nat := sorry

/-- Hoare triple for mmaximum2 (right-to-left, returns last) -/
theorem mmaximum2_spec (v : Array Int) (h : v.size > 0) :
    ⦃⌜v.size > 0⌝⦄ 
    mmaximum2 v
    ⦃⇓i => ⌜0 ≤ i ∧ i < v.size ∧ ∀ k, 0 ≤ k ∧ k < v.size → v[i]! ≥ v[k]!⌝⦄ := by
  sorry

/-- Implementation placeholder for mfirstMaximum -/
def mfirstMaximum (v : Array Int) : Id Nat := sorry

/-- Hoare triple for mfirstMaximum (returns first occurrence) -/
theorem mfirstMaximum_spec (v : Array Int) (h : v.size > 0) :
    ⦃⌜v.size > 0⌝⦄ 
    mfirstMaximum v
    ⦃⇓i => ⌜0 ≤ i ∧ i < v.size ∧ 
           (∀ k, 0 ≤ k ∧ k < v.size → v[i]! ≥ v[k]!) ∧
           (∀ l, 0 ≤ l ∧ l < i → v[i]! > v[l]!)⌝⦄ := by
  sorry

/-- Implementation placeholder for mlastMaximum -/
def mlastMaximum (v : Array Int) : Id Nat := sorry

/-- Hoare triple for mlastMaximum (returns last occurrence) -/
theorem mlastMaximum_spec (v : Array Int) (h : v.size > 0) :
    ⦃⌜v.size > 0⌝⦄ 
    mlastMaximum v
    ⦃⇓i => ⌜0 ≤ i ∧ i < v.size ∧ 
           (∀ k, 0 ≤ k ∧ k < v.size → v[i]! ≥ v[k]!) ∧
           (∀ l, i < l ∧ l < v.size → v[i]! > v[l]!)⌝⦄ := by
  sorry

/-- Implementation placeholder for mmaxvalue1 -/
def mmaxvalue1 (v : Array Int) : Id Int := sorry

/-- Hoare triple for mmaxvalue1 (returns max value, left-to-right) -/
theorem mmaxvalue1_spec (v : Array Int) (h : v.size > 0) :
    ⦃⌜v.size > 0⌝⦄ 
    mmaxvalue1 v
    ⦃⇓m => ⌜(∃ j, 0 ≤ j ∧ j < v.size ∧ v[j]! = m) ∧
           (∀ k, 0 ≤ k ∧ k < v.size → m ≥ v[k]!)⌝⦄ := by
  sorry

/-- Implementation placeholder for mmaxvalue2 -/
def mmaxvalue2 (v : Array Int) : Id Int := sorry

/-- Hoare triple for mmaxvalue2 (returns max value, right-to-left) -/
theorem mmaxvalue2_spec (v : Array Int) (h : v.size > 0) :
    ⦃⌜v.size > 0⌝⦄ 
    mmaxvalue2 v
    ⦃⇓m => ⌜(∃ j, 0 ≤ j ∧ j < v.size ∧ v[j]! = m) ∧
           (∀ k, 0 ≤ k ∧ k < v.size → m ≥ v[k]!)⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseMaximum