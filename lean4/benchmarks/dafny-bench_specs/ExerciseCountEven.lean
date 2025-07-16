import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Exercise: Count Even Numbers

This module ports the Dafny specification for counting even numbers
in a sequence of non-negative integers.

The specification includes:
- A predicate `positive` that checks if all elements are non-negative
- A predicate `isEven` that checks if a number is even
- A function `CountEven` that counts even numbers in a sequence
- A method `mcountEven` that implements the counting algorithm
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseCountEven

/-- Predicate: all elements in the list are non-negative -/
def positive (s : List Int) : Prop :=
  ∀ u : Nat, u < s.length → s[u]! ≥ 0

/-- Predicate: check if a non-negative integer is even -/
def isEven (i : Nat) : Bool :=
  i % 2 = 0

/-- Function: count even numbers in a sequence of non-negative integers -/
def CountEven (s : List Int) (h : positive s) : Int :=
  sorry  -- Placeholder implementation

/-- Array facts that are useful for proofs -/
theorem ArrayFacts :
  (∀ (T : Type) (v : Array T), v.toList = v.toList) ∧
  (∀ (T : Type) (v : Array T), v.toList.length = v.size) ∧
  (∀ (T : Type) (v : Array T) (k : Nat), k < v.size → 
    (v.toList.take (k + 1)).take k = v.toList.take k) := by
  sorry

/-- Implementation placeholder for mcountEven -/
def mcountEven (v : Array Int) : Id Int := sorry

/-- Hoare triple for mcountEven -/
theorem mcountEven_spec (v : Array Int) (h : positive v.toList) :
    ⦃⌜positive v.toList⌝⦄ 
    mcountEven v
    ⦃⇓n => ⌜n = CountEven v.toList h⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseCountEven