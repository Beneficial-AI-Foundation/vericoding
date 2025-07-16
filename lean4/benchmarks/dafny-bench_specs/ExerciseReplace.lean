import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Exercise: Replace

This module ports the Dafny specification for replacing all occurrences of
a value in an array with another value.

The specification includes:
- A method `replace` that replaces all occurrences of x with y in array v
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseReplace

/-- Implementation placeholder for replace -/
def replace (v : Array Int) (x y : Int) : StateM (Array Int) Unit := sorry

/-- Hoare triple for replace -/
theorem replace_spec (v : Array Int) (x y : Int) :
    ⦃⌜True⌝⦄ 
    StateT.run (replace v x y) v
    ⦃⇓(_, v') => ⌜(∀ k : Nat, k < v.size → v[k]! = x → v'[k]! = y) ∧
                  (∀ k : Nat, k < v.size → v[k]! ≠ x → v'[k]! = v[k]!)⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseReplace