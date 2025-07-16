import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Synthesis Task: Sum of Negatives

This module ports the Dafny synthesis task for calculating the sum of negative values in an array.

The specification includes:
- A recursive function `sumNegativesTo` that computes the sum of negative values up to index n
- A method `sumOfNegatives` that returns the sum of all negative values in the array
-/

namespace NumpySpec.DafnyBenchmarks.SynthesisSumOfNegatives

/-- Recursive function to sum negative values up to index n -/
def sumNegativesTo (a : Array Int) (n : Nat) : Int :=
  if h : n = 0 then 
    0 
  else if h' : n ≤ a.size then
    if a[n-1]'(by omega) < 0 then 
      sumNegativesTo a (n-1) + a[n-1]'(by omega)
    else 
      sumNegativesTo a (n-1)
  else
    0

/-- Implementation placeholder for sumOfNegatives -/
def sumOfNegatives (a : Array Int) : Id Int := sorry

/-- Hoare triple for sumOfNegatives -/
theorem sumOfNegatives_spec (a : Array Int) :
    ⦃⌜True⌝⦄ 
    sumOfNegatives a
    ⦃⇓result => ⌜result = sumNegativesTo a a.size⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisSumOfNegatives