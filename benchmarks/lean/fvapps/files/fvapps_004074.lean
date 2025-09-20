-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Array.getSum (arr : Array Int) (n : Nat) : Int :=
  sorry

def Array.getMean (arr : Array Int) (x y : Int) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_x_returns_negative_one {arr : Array Int} {x y : Int} :
  arr.size > 0 → x ≤ 0 → Array.getMean arr x y = -1 :=
sorry

theorem invalid_y_returns_negative_one {arr : Array Int} {x y : Int} :
  arr.size > 0 → y ≤ 0 → Array.getMean arr x y = -1 :=
sorry

theorem indices_larger_than_array {arr : Array Int} {x y : Int} :
  x > arr.size ∨ y > arr.size →
  Array.getMean arr x y = -1 :=
sorry

theorem mean_properties {arr : Array Int} {x y : Int} :
  arr.size ≥ 2 →
  1 < x ∧ x ≤ arr.size →
  1 < y ∧ y ≤ arr.size →
  let firstMean := Float.ofInt (Array.getSum arr x.toNat) / Float.ofInt x;
  let secondMean := Float.ofInt (Array.getSum (arr.extract (arr.size - y.toNat) arr.size) y.toNat) / Float.ofInt y;
  let expected := (firstMean + secondMean) / 2;
  (Array.getMean arr x y - expected).abs < 1e-10 :=
sorry
-- </vc-theorems>