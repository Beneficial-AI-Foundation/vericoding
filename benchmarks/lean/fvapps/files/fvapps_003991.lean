-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def process_data : List (List Int) → Int := sorry

theorem process_data_permutation_invariant (data : List (List Int)) 
  (h : ∀ l ∈ data, l.length = 2 ∧ l[0]! ≠ l[1]!) :
  process_data data = process_data (data.reverse) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem process_data_positive_output 
  (data : List (List Int))
  (h1 : ∀ l ∈ data, l.length = 2)
  (h2 : ∀ l ∈ data, 1 ≤ l[0]! ∧ l[0]! ≤ 100)
  (h3 : ∀ l ∈ data, 0 ≤ l[1]! ∧ l[1]! ≤ 99)
  (h4 : ∀ l ∈ data, l[0]! > l[1]!)
  (h5 : data ≠ []) :
  process_data data > 0 := sorry
-- </vc-theorems>