import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Find the first occurrence of a key in an array.
    
    Returns the index of the first occurrence of the key, or -1 if not found.
    
    Preconditions:
    - Array is not null (always true in Lean)
    
    Postconditions:
    - If result ≥ 0: 
      - result is a valid index in the array
      - a[result] = key
      - result is the smallest such index
    - If result < 0:
      - The key does not exist in the array
-/
def find (a : Array Int) (key : Int) : Int := sorry

theorem find_spec (a : Array Int) (key : Int) :
    ⦃⌜True⌝⦄
    (pure (find a key) : Id _)
    ⦃⇓i => ⌜(0 ≤ i → (i < a.size ∧ 
                       a[i.toNat]! = key ∧
                       ∀ k : Nat, 0 ≤ k ∧ k < i → a[k]! ≠ key)) ∧
            (i < 0 → ∀ k : Nat, 0 ≤ k ∧ k < a.size → a[k]! ≠ key)⌝⦄ := by
  mvcgen [find]
  sorry
