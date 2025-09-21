-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def insert (line : Array Char) (l : Int) (nl : Array Char) (p : Int) (_ : Int) : Array Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem insert_spec (line : Array Char) (l : Int) (nl : Array Char) (p : Int) (_at : Int) :
0 ≤ l + p ∧ l + p ≤ line.size ∧
0 ≤ p ∧ p ≤ nl.size ∧
0 ≤ _at ∧ _at ≤ l →
let result := insert line l nl p _at

-- Simplified postconditions focusing on basic properties

result.size = line.size ∧

∀ i, 0 ≤ i ∧ i < _at → result[i.toNat]! = line[i.toNat]! ∧

∀ i, 0 ≤ i ∧ i < p → result[(_at + i).toNat]! = nl[i.toNat]! :=
sorry
-- </vc-theorems>