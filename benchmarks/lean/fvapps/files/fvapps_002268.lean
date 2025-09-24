-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : Nat × String := sorry

theorem solve_output_structure (s : String) : 
  let result := solve s
  (result.1 = result.2.length) ∧ 
  (∀ c, c ∈ result.2.data → c = 'L' ∨ c = 'R' ∨ c = 'U' ∨ c = 'D') := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_output_balanced (s : String) :
  let result := solve s
  let path := result.2
  (path.data.count 'L' = path.data.count 'R') ∧
  (path.data.count 'U' = path.data.count 'D') := sorry

theorem solve_output_length_bounds (s : String) :
  let result := solve s
  let l := s.data.count 'L'
  let r := s.data.count 'R'
  let u := s.data.count 'U'
  let d := s.data.count 'D'
  (result.1 ≤ 2 * min l r + 2 * min u d) ∧
  (result.1 % 2 = 0) := sorry

theorem solve_empty_conditions (s : String) :
  let result := solve s
  let l := s.data.count 'L'
  let r := s.data.count 'R'
  let u := s.data.count 'U'
  let d := s.data.count 'D'
  (min l r = 0 ∧ min u d = 0 → result = (0, "")) ∧
  (¬(min l r = 0 ∧ min u d = 0) → result.1 > 0) := sorry
-- </vc-theorems>