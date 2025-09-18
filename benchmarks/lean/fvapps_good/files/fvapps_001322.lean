-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_restaurant_device (k : String) (n : Int) : Int := sorry

theorem output_bound 
  (k : String) 
  (n : Int)
  (h1 : k.length = 3) 
  (h2 : ∀ c ∈ k.data, '0' <= c ∧ c <= '9')
  (h3 : 0 ≤ n ∧ n ≤ 100) :
  0 ≤ solve_restaurant_device k n ∧ solve_restaurant_device k n ≤ 1000 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_output_before_five
  (k : String)
  (n : Int)
  (h1 : k.length = 3)
  (h2 : ∀ c ∈ k.data, '0' <= c ∧ c <= '9')
  (h3 : n ≤ 4) :
  solve_restaurant_device k n = 0 := sorry

theorem output_formula
  (k : String)
  (n : Int)
  (h1 : k.length = 3)
  (h2 : ∀ c ∈ k.data, '0' <= c ∧ c <= '9')
  (h3 : 5 ≤ n ∧ n ≤ 100) :
  solve_restaurant_device k n = (k.data.eraseDups.length)^3 := sorry

theorem deterministic
  (k : String)
  (n : Int)
  (h1 : k.length = 3)
  (h2 : ∀ c ∈ k.data, '0' <= c ∧ c <= '9') :
  solve_restaurant_device k n = solve_restaurant_device k n := sorry
-- </vc-theorems>