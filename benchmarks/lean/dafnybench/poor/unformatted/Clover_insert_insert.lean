


/-!
{
"name": "Clover_insert_insert",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_insert_insert",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Insert characters from one array into another at a specified position.

@param line The destination array to insert into
@param l Length of valid data in line array
@param nl Source array to insert from
@param p Number of characters to insert
@param at Position to insert at
-/
def insert (line : Array Char) (l : Int) (nl : Array Char) (p : Int) (_ : Int) : Array Char := sorry

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
theorem insert_spec (line : Array Char) (l : Int) (nl : Array Char) (p : Int) (_at : Int) :
0 ≤ l + p ∧ l + p ≤ line.size ∧
0 ≤ p ∧ p ≤ nl.size ∧
0 ≤ _at ∧ _at ≤ l →
let result := insert line l nl p _at
-- Simplified postconditions focusing on basic properties
result.size = line.size ∧
∀ i, 0 ≤ i ∧ i < _at → result[i.toNat]! = line[i.toNat]! ∧
∀ i, 0 ≤ i ∧ i < p → result[(_at + i).toNat]! = nl[i.toNat]! := sorry