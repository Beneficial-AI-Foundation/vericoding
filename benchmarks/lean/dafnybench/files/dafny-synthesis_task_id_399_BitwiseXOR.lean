-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BitwiseXOR (a b : Array UInt32) : Array UInt32 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BitwiseXOR_spec (a b : Array UInt32) :
a.size = b.size →
let result := BitwiseXOR a b
result.size = a.size ∧
∀ i, 0 ≤ i ∧ i < result.size →
result[i]! = (a[i]!).xor (b[i]!) :=
sorry
-- </vc-theorems>