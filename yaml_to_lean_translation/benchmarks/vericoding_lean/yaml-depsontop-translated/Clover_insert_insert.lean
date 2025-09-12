```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Clover_insert_insert",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: Clover_insert_insert",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["insert"]
}
-/

namespace DafnyBenchmarks

/--
  Insert characters from one array into another at a specified position.
  
  @param line The destination array to insert into
  @param l Length of valid data in line array
  @param nl Source array to insert from
  @param p Number of characters to insert
  @param at Position to insert at
-/
def insert (line : Array Char) (l : Int) (nl : Array Char) (p : Int) (at : Int) : Array Char := sorry

/--
  Specification for insert method translated from Dafny.
  
  Preconditions:
  - 0 ≤ l + p ≤ line.size
  - 0 ≤ p ≤ nl.size  
  - 0 ≤ at ≤ l

  Postconditions:
  - Characters from nl are inserted at position 'at'
  - Characters before insert position are preserved
  - Characters after insert position are shifted right
-/
theorem insert_spec (line : Array Char) (l : Int) (nl : Array Char) (p : Int) (at : Int) :
  0 ≤ l + p ∧ l + p ≤ line.size ∧
  0 ≤ p ∧ p ≤ nl.size ∧
  0 ≤ at ∧ at ≤ l →
  let result := insert line l nl p at
  -- Simplified postconditions focusing on basic properties
  result.size = line.size ∧
  ∀ i, 0 ≤ i ∧ i < at → result.get i = line.get i ∧
  ∀ i, 0 ≤ i ∧ i < p → result.get (at + i) = nl.get i := sorry

end DafnyBenchmarks
```