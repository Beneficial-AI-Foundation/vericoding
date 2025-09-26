-- <vc-preamble>
inductive Color where
| Red : Color
| White : Color
| Blue : Color
deriving Repr, BEq, Inhabited
def Below (c d : Color) : Bool :=
match c, d with
| Color.Red, _ => true
| _, Color.Blue => true
| c1, c2 => c1 == c2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DutchFlag (a : Array Color) : Array Color :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem DutchFlag_spec (a : Array Color) :
let result := DutchFlag a

-- Colors are properly ordered

(∀ i j, 0 ≤ i → i < j → j < result.size → Below (result[i]!) (result[j]!)) ∧

-- Array contents are preserved (multiset equality)

(result.toList = a.toList) :=
sorry
-- </vc-theorems>