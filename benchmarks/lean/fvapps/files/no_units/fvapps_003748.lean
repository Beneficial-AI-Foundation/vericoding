-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_int_inrange (a b : Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem range_order_invariant (a b : Int) 
  (h1 : 1 ≤ a) (h2 : a ≤ 1000) (h3 : 1 ≤ b) (h4 : b ≤ 1000) (h5 : a ≤ b) :
  let result := find_int_inrange a b
  ∀ x ∈ result, x ∈ result → (∃ n : Int, x = n) ∧
  (result.length > 1 → result[1]! ≥ a ∧ result[1]! ≤ b) :=
sorry

theorem single_point_range (n : Int) 
  (h1 : 1 ≤ n) (h2 : n ≤ 1000) :
  let result := find_int_inrange n n
  result.length ≥ 1 ∧ ∀ x ∈ result, ∃ m : Int, x = m :=
sorry

theorem window_properties (start width : Int)
  (h1 : 100 ≤ start) (h2 : start ≤ 900)
  (h3 : 1 ≤ width) (h4 : width ≤ 100) :
  let result := find_int_inrange start (start + width)
  result.length ≥ 1 ∧
  (result.length > 1 →
    ∀ x ∈ result.tail, start ≤ x ∧ x ≤ start + width) :=
sorry
-- </vc-theorems>