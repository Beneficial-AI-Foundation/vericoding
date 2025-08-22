import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- FindEvenNumbers: Extract all even numbers from an array.

    Given an array of integers, returns a new array containing only the even numbers
    from the input array, preserving their relative order.

    The specification ensures:
    - All even numbers from the input are included in the result
    - No numbers not in the input appear in the result  
    - All numbers in the result are even
    - The relative order of even numbers is preserved
-/
def findEvenNumbers (arr : Array Int) : Id (Array Int) :=
  arr.filter (fun x => x % 2 = 0)

/-- Specification: findEvenNumbers returns an array containing exactly the even numbers
    from the input array in their original order.

    Precondition: True (no special preconditions)
    Postcondition:
    - Every even number in arr appears in the result
    - Every number not in arr does not appear in the result
    - Every number in the result is even
    - The relative order of even numbers is preserved
-/
theorem findEvenNumbers_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    findEvenNumbers arr
    ⦃⇓result => ⌜(∀ x : Int, x ∈ arr.toList ∧ x % 2 = 0 → x ∈ result.toList) ∧
                 (∀ x : Int, x ∉ arr.toList → x ∉ result.toList) ∧
                 (∀ i : Fin result.size, result[i] % 2 = 0) ∧
                 (∀ i j : Fin result.size, i < j → 
                   ∃ n m : Fin arr.size, n < m ∧ result[i] = arr[n] ∧ result[j] = arr[m])⌝⦄ := by
  mvcgen [findEvenNumbers]
  sorry