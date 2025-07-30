import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Counts the number of non-zero values in a vector.
    
    The word "non-zero" is in reference to the Python 2.x
    built-in method `__nonzero__()` (renamed `__bool__()`
    in Python 3.x) of Python objects that tests an object's
    "truthfulness". For example, any number is considered
    truthful if it is nonzero, whereas any string is considered
    truthful if it is not the empty string. Thus, this function
    counts how many elements in the vector are non-zero. -/
def count_nonzero {n : Nat} (a : Vector Int n) : Id Nat :=
  sorry

/-- Specification: count_nonzero returns the number of non-zero elements in the vector.
    
    The function counts exactly those elements that are not equal to zero.
    The result is always between 0 and n (inclusive), where n is the length of the vector.
    If all elements are zero, the result is 0.
    If all elements are non-zero, the result is n. -/
theorem count_nonzero_spec {n : Nat} (a : Vector Int n) :
    ⦃⌜True⌝⦄
    count_nonzero a
    ⦃⇓count => ⌜count ≤ n ∧ 
                (n = 0 → count = 0) ∧
                (∀ i : Fin n, a.get i = 0) → count = 0 ∧
                (∀ i : Fin n, a.get i ≠ 0) → count = n ∧
                (∃ i : Fin n, a.get i ≠ 0) → count > 0 ∧
                (∃ i : Fin n, a.get i = 0) → count < n⌝⦄ := by
  sorry