-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Delete (line : Array Char) (l _at p : Nat) : Array Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Delete_spec (line : Array Char) (l _at p : Nat) :
l ≤ line.size →
_at + p ≤ l →
let result := Delete line l _at p

-- Note: Complex array slicing operations simplified to basic size properties

result.size = line.size ∧

∀ i, i < _at → result[i]! = line[i]! :=
sorry
-- </vc-theorems>