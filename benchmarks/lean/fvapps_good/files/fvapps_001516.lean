-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_wealth_disparity (n : Nat) (wealth : List Int) (managers : List Int) : Int :=
  sorry

-- Theorem stating that result is bounded by max wealth difference
-- </vc-definitions>

-- <vc-theorems>
theorem max_wealth_disparity_bounded (n : Nat) (wealth : List Int) (managers : List Int)
  (h1 : 2 ≤ n) (h2 : n ≤ 10)
  (h3 : ∀ w ∈ wealth, -100 ≤ w ∧ w ≤ 100)
  (h4 : managers.length = n)
  (h5 : wealth.length = n)
  (h6 : ∀ i ∈ managers, i = 2 ∨ i = -1)
  (h7 : managers[1] = -1) :
  let result := find_max_wealth_disparity n wealth managers
  let max_val := wealth.foldl max (wealth.head!)
  let min_val := wealth.foldl min (wealth.head!)
  result ≤ max_val - min_val := sorry

-- Theorem stating that result is finite and bounded

theorem max_wealth_disparity_finite (n : Nat) (wealth : List Int) (managers : List Int) 
  (h1 : 2 ≤ n) (h2 : n ≤ 10)
  (h3 : ∀ w ∈ wealth, -100 ≤ w ∧ w ≤ 100)
  (h4 : managers.length = n)
  (h5 : wealth.length = n)
  (h6 : ∀ i ∈ managers, i = 2 ∨ i = -1)
  (h7 : managers[1] = -1) : 
  -200 ≤ find_max_wealth_disparity n wealth managers ∧ 
  find_max_wealth_disparity n wealth managers ≤ 200 := sorry
-- </vc-theorems>