import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- insert: Insert a portion of one array into another array at a specified position.

    Modifies the 'line' array by inserting 'p' characters from 'nl' starting at position 'at'.
    The insertion shifts existing characters to make room.

    Parameters:
    - line: The target array to modify
    - l: The current length of content in line
    - nl: The source array containing characters to insert
    - p: The number of characters to insert from nl
    - pos: The position in line where insertion should occur
-/
def insert (line : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (pos : Nat) : Array Char :=
  if l + p ≤ line.size ∧ p ≤ nl.size ∧ pos ≤ l then
    (
      line.extract 0 pos ++ 
      nl.extract 0 p ++ 
      line.extract pos l ++ 
      Array.mk (List.replicate p ' ')
    )
  else
    line

/-- Specification: insert modifies the line array by inserting p characters from nl at position pos,
    preserving the original content before and after the insertion point.

    Precondition:
    - 0 ≤ l + p ≤ line.size (enough space for insertion)
    - 0 ≤ p ≤ nl.size (valid source range)
    - 0 ≤ pos ≤ l (valid insertion position)
    
    Postcondition:
    - Characters from nl[0..p) are copied to line[pos..pos+p)
    - Characters before position 'pos' remain unchanged
    - Characters originally at positions [pos..l) are shifted to positions [pos+p..l+p)
-/
theorem insert_spec (line : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (pos : Nat) :
    ⦃⌜0 ≤ l + p ∧ l + p ≤ line.size ∧ 0 ≤ p ∧ p ≤ nl.size ∧ 0 ≤ pos ∧ pos ≤ l⌝⦄
    (pure (insert line l nl p pos) : Id _)
    ⦃⇓result => ⌜(∀ i : Nat, i < p → result[pos + i]! = nl[i]!) ∧
                 (∀ i : Nat, i < pos → result[i]! = line[i]!) ∧
                 (∀ i : Nat, pos + p ≤ i ∧ i < l + p → result[i]! = line[i - p]!)⌝⦄ := by
  sorry
