-- <vc-preamble>
def abs (x : Float) : Float :=
if x < 0 then -x else x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_close_elements (numbers : Array Float) (threshold : Float) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem has_close_elements_spec (numbers : Array Float) (threshold : Float) :
let result := has_close_elements numbers threshold
result ↔ (∃ i j : Nat,
i < numbers.size ∧
j < numbers.size ∧
i ≠ j ∧
abs (numbers[i]! - numbers[j]!) < threshold) ∧
(result → numbers.size > 1) :=
sorry
-- </vc-theorems>