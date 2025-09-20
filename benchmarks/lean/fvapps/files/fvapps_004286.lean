-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numberOfSteps (steps m : Nat) : Int := sorry

theorem result_is_negative_one_or_not_less_than_half_steps {steps m : Nat} (h1 : steps > 0) (h2 : m > 0) :
  let result := numberOfSteps steps m
  result = -1 ∨ result ≥ steps / 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_divisible_by_m_or_negative_one {steps m : Nat} (h1 : steps > 0) (h2 : m > 0) :
  let result := numberOfSteps steps m
  result = -1 ∨ result % m = 0 := sorry

theorem negative_one_when_steps_less_than_m {steps m : Nat} (h1 : steps > 0) (h2 : m > 0) :
  steps < m → numberOfSteps steps m = -1 := sorry

theorem even_steps_special_case {steps m : Nat} (h1 : steps > 1) (h2 : m > 0) 
  (h3 : steps % 2 = 0) (h4 : steps ≥ m) (h5 : (steps / 2) % m = 0) :
  numberOfSteps steps m = steps / 2 := sorry
-- </vc-theorems>