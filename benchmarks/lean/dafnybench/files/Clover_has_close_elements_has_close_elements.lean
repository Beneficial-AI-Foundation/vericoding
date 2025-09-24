-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_close_elements (numbers : Array Float) (threshold : Float) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem has_close_elements_spec
(numbers : Array Float) (threshold : Float) :
threshold ≥ 0 →
let res := has_close_elements numbers threshold
(res → ∃ i j : Int,
0 ≤ i ∧ i < numbers.size ∧
0 ≤ j ∧ j < numbers.size ∧
i ≠ j ∧
(if numbers[i.toNat]! - numbers[j.toNat]! < 0
then numbers[j.toNat]! - numbers[i.toNat]!
else numbers[i.toNat]! - numbers[j.toNat]!) < threshold) ∧
(!res → ∀ i j : Int,
1 ≤ i ∧ i < numbers.size ∧
0 ≤ j ∧ j < i →
(if numbers[i.toNat]! - numbers[j.toNat]! < 0
then numbers[j.toNat]! - numbers[i.toNat]!
else numbers[i.toNat]! - numbers[j.toNat]!) ≥ threshold) :=
sorry
-- </vc-theorems>