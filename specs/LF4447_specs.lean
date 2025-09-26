-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pay_cheese (wheels : List Nat) : String := sorry

theorem pay_cheese_format (wheels : List Nat) (h : wheels.length = 5) :
  let result := pay_cheese wheels
  ∃ n : Nat, result = "£" ++ toString n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pay_cheese_payment_bounds (wheels : List Nat) (h : wheels.length = 5) :
  let result := pay_cheese wheels
  let total := wheels.foldl (· + ·) 0 
  let min_expected := ((total / 100) * 875) / 100 * 4
  let max_expected := (((total / 100) + 1) * 875) / 100 * 4
  let actual := (result.drop 1).toNat!
  min_expected ≤ actual ∧ actual ≤ max_expected := sorry

theorem pay_cheese_zero (wheels : List Nat) (h : wheels.length = 5) :
  wheels.foldl (· + ·) 0 = 0 → pay_cheese wheels = "£0" := sorry
-- </vc-theorems>