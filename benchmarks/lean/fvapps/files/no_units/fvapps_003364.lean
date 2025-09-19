-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def odd_ones_out (xs : List Int) : List Int := sorry

theorem odd_ones_out_preserves_pairs {xs : List Int} (h : xs ≠ []) :
  odd_ones_out xs = xs.filter (fun x => (xs.count x) % 2 = 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_ones_out_elements_from_input {xs : List Int} (h : xs ≠ []) :
  ∀ x ∈ odd_ones_out xs, x ∈ xs := sorry 

theorem odd_ones_out_even_counts {xs : List Int} (h : xs ≠ []) :
  ∀ x ∈ odd_ones_out xs, (odd_ones_out xs).count x % 2 = 0 := sorry

theorem odd_ones_out_maintains_order {xs : List Int} (h : xs ≠ []) : 
  odd_ones_out xs = xs.filter (fun x => xs.count x % 2 = 0) := sorry
-- </vc-theorems>