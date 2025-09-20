-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (nums : List Int) (div : Int) : List Int := sorry

theorem solve_output_length {nums : List Int} {div : Int} (h : div > 0) :
  (solve nums div).length = nums.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_elements_geq_input {nums : List Int} {div : Int} (h : div > 0) :
  ∀ (i : Nat), i < nums.length → 
    ((solve nums div).get ⟨i, by sorry⟩) ≥ (nums.get ⟨i, by sorry⟩) := sorry

theorem solve_diff_less_than_div {nums : List Int} {div : Int} (h : div > 0) :
  ∀ (i : Nat), i < nums.length →
    ((solve nums div).get ⟨i, by sorry⟩) - (nums.get ⟨i, by sorry⟩) < div := sorry

theorem solve_div_one {nums : List Int} :
  solve nums 1 = nums := sorry

theorem solve_empty {div : Int} (h : div > 0) :
  solve [] div = [] := sorry
-- </vc-theorems>