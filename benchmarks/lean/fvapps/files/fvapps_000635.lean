-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_second_largest (l: List Int) : Int := sorry 

theorem find_second_largest_from_list {l: List Int} 
  (h1: l.length ≥ 3) 
  (h2: ∀ (x y: Int), x ∈ l → y ∈ l → x = y → x = y) :
  find_second_largest l ∈ l := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_second_largest_less_than_max {l: List Int}
  (h1: l.length ≥ 3)
  (h2: ∀ (x y: Int), x ∈ l → y ∈ l → x = y → x = y) :
  ∃ x, x ∈ l ∧ x > find_second_largest l := sorry

theorem find_second_largest_greater_than_min {l: List Int}
  (h1: l.length ≥ 3)
  (h2: ∀ (x y: Int), x ∈ l → y ∈ l → x = y → x = y) :
  ∃ x, x ∈ l ∧ x < find_second_largest l := sorry
-- </vc-theorems>