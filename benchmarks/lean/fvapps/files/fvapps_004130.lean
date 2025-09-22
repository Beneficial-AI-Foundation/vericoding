-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ex_euler (n : Int) : Float := sorry

theorem ex_euler_output_range (n : Nat) (h : n > 0) : 
  let result := ex_euler n
  0 ≤ result ∧ result ≤ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ex_euler_decreases (n : Nat) (h : n ≥ 2) :
  let error1 := ex_euler n
  let error2 := ex_euler (2 * n)
  error2 ≤ 1.5 * error1 := sorry

theorem ex_euler_precision (n : Nat) (h : n > 0) :
  let result := ex_euler n
  result = Float.floor (result * 1e6) / 1e6 := sorry

theorem ex_euler_invalid :
  ∀ n : Int, n ≤ 0 → ex_euler n = 0 := sorry
-- </vc-theorems>