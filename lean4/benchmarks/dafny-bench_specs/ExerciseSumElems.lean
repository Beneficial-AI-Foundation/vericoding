import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Exercise: Sum of Elements

This module ports the Dafny specification for computing the sum of elements
in a sequence/array.

The specification includes:
- Two sum functions: `SumR` (right-to-left) and `SumL` (left-to-right)
- Lemmas proving that both sum functions are equivalent
- Lemmas about sum decomposition (sum by parts)
- Methods `sumElems` and `sumElemsB` that compute the sum of array elements
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseSumElems

/-- Sum function - right to left (from end) -/
def SumR (s : List Int) : Int :=
  sorry  -- Placeholder implementation

/-- Sum function - left to right (from beginning) -/
def SumL : List Int → Int
  | [] => 0
  | h :: t => h + SumL t

/-- Lemma: concatenation preserves last element extraction -/
theorem concatLast (s t : List Int) (h : t ≠ []) :
  (s ++ t).dropLast = s ++ t.dropLast := by
  sorry

/-- Lemma: concatenation preserves tail extraction -/
theorem concatFirst (s t : List Int) (h : s ≠ []) :
  (s ++ t).tail = s.tail ++ t := by
  sorry

/-- Lemma: SumR distributes over concatenation -/
theorem SumByPartsR (s t : List Int) :
  SumR (s ++ t) = SumR s + SumR t := by
  sorry

/-- Lemma: SumL distributes over concatenation -/
theorem SumByPartsL (s t : List Int) :
  SumL (s ++ t) = SumL s + SumL t := by
  sorry

/-- Lemma: SumR and SumL are equal for any sublist -/
theorem equalSumR (s : List Int) (i j : Nat) (h : i ≤ j ∧ j ≤ s.length) :
  SumR (s.drop i |>.take (j - i)) = SumL (s.drop i |>.take (j - i)) := by
  sorry

/-- Lemma: SumR and SumL are equal for array slices -/
theorem equalSumsV (v : Array Int) (i j : Nat) (h : i ≤ j ∧ j ≤ v.size) :
  SumR (v.toList.drop i |>.take (j - i)) = SumL (v.toList.drop i |>.take (j - i)) := by
  sorry

/-- Sum function for array slice -/
def SumV (v : Array Int) (c f : Nat) (h : c ≤ f ∧ f ≤ v.size) : Int :=
  SumR (v.toList.drop c |>.take (f - c))

/-- Array facts that are useful for proofs -/
theorem ArrayFacts :
  (∀ v : Array Int, v.toList = v.toList) ∧
  (∀ v : Array Int, v.toList.length = v.size) ∧
  (∀ v : Array Int, ∀ k : Nat, k < v.size → (v.toList.take (k + 1)).take k = v.toList.take k) := by
  sorry

/-- Implementation placeholder for sumElems -/
def sumElems (v : Array Int) : Id Int := sorry

/-- Hoare triple for sumElems -/
theorem sumElems_spec (v : Array Int) :
    ⦃⌜True⌝⦄ 
    sumElems v
    ⦃⇓sum => ⌜sum = SumR v.toList⌝⦄ := by
  sorry

/-- Implementation placeholder for sumElemsB -/
def sumElemsB (v : Array Int) : Id Int := sorry

/-- Hoare triple for sumElemsB -/
theorem sumElemsB_spec (v : Array Int) :
    ⦃⌜True⌝⦄ 
    sumElemsB v
    ⦃⇓sum => ⌜sum = SumR v.toList⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseSumElems