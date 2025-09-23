-- <vc-preamble>
partial def Power (base : Int) (exponent : Int) : Int :=
if exponent == 0 then 1
else base * Power base (exponent - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def PowerOfListElements (l : Array Int) (n : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Power_spec (base : Int) (exponent : Int) :
exponent ≥ 0 → Power base exponent ≥ 0 :=
sorry

theorem PowerOfListElements_spec (l : Array Int) (n : Int) :
n ≥ 0 →
let result := PowerOfListElements l n
result.size = l.size ∧
∀ i, 0 ≤ i ∧ i < l.size → result[i]! = Power l[i]! n :=
sorry
-- </vc-theorems>