-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def counting_bits (n : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem counting_bits_spec (n : Int) :
0 ≤ n ∧ n ≤ 100000 →
let result := counting_bits n
result.size = n + 1 ∧
∀ i, 1 ≤ i ∧ i < n + 1 → result[i.toNat]! = result[(i / 2).toNat]! + i % 2 :=
sorry
-- </vc-theorems>