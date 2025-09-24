-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_probability (n : Int) : Float := sorry

theorem probability_bounds (n : Int) : 
  0 ≤ calculate_probability n ∧ calculate_probability n ≤ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem monotonic_increase {n1 n2 : Int} (h : n1 > n2) (h1 : n1 ≤ 365) (h1b : 1 ≤ n1) (h2 : n2 ≤ 365) (h2b : 0 ≤ n2) :
  calculate_probability n1 ≥ calculate_probability n2 := sorry

theorem zero_or_one_person (n : Int) (h : n ≤ 1) :
  calculate_probability n = 0 := sorry

theorem over_365_people (n : Int) (h : n ≥ 366) :
  calculate_probability n = 1 := sorry

theorem decimal_places_bound (n : Int) (h1 : 2 ≤ n) (h2 : n ≤ 365) :
  ∃ k : Float, k = calculate_probability n ∧ k * 100 = Float.round (k * 100) := sorry
-- </vc-theorems>