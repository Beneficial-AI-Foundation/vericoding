import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- only_once: Check if an element appears exactly once in an array.
    
    Given an array and a key element, returns true if and only if the key
    appears exactly once in the array.
    
    Example: only_once([1, 2, 3, 2, 4], 3) = true
             only_once([1, 2, 3, 2, 4], 2) = false
-/
def onlyOnce {α : Type} [BEq α] (a : Array α) (key : α) : Id Bool :=
  let rec countOccurrences (i : Nat) (count : Nat) : Nat :=
    if h : i < a.size then
      if a[i] == key then
        countOccurrences (i + 1) (count + 1)
      else
        countOccurrences (i + 1) count
    else
      count
  countOccurrences 0 0 == 1

/-- Specification: only_once returns true iff the key appears exactly once.
    
    Precondition: True (no special preconditions)
    Postcondition: Result is true iff the count of key in the array equals 1
-/
theorem onlyOnce_spec {α : Type} [BEq α] [LawfulBEq α] (a : Array α) (key : α) :
    ⦃⌜True⌝⦄
    onlyOnce a key
    ⦃⇓b => ⌜b ↔ (a.toList.count key = 1)⌝⦄ := by
  sorry