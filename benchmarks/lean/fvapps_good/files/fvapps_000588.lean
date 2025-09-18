-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countChar (s : String) (c : Char) : Nat := sorry

def solve_robot_safety (n m : Nat) (commands : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_robot_safety_returns_valid_output 
  (n m : Nat) (commands : String)
  (h1 : 0 < n) (h2 : 0 < m)
  (h3 : commands.length > 0)
  (h4 : ∀ c ∈ commands.data, c = 'U' ∨ c = 'D' ∨ c = 'L' ∨ c = 'R') :
  solve_robot_safety n m commands = "safe" ∨ 
  solve_robot_safety n m commands = "unsafe" := sorry

theorem single_direction_unsafe_up_down
  (n m : Nat) (commands : String)
  (h1 : 0 < n) (h2 : 0 < m)
  (h3 : commands.length > n)
  (h4 : ∀ c ∈ commands.data, c = 'U' ∨ c = 'D') :
  solve_robot_safety n m commands = "unsafe" := sorry

theorem single_direction_unsafe_left_right
  (n m : Nat) (commands : String)
  (h1 : 0 < n) (h2 : 0 < m)
  (h3 : commands.length > m)
  (h4 : ∀ c ∈ commands.data, c = 'L' ∨ c = 'R') :
  solve_robot_safety n m commands = "unsafe" := sorry

theorem returns_to_origin_safe
  (n m : Nat) (commands : String)
  (h1 : 0 < n) (h2 : 0 < m) 
  (h3 : n > commands.length)
  (h4 : m > commands.length)
  (h5 : (countChar commands 'U') = (countChar commands 'D'))
  (h6 : (countChar commands 'L') = (countChar commands 'R')) :
  solve_robot_safety n m commands = "safe" := sorry

theorem opposite_moves_require_space
  (n m : Nat) (commands : String)
  (h1 : 0 < n) (h2 : 0 < m)
  (h3 : ((countChar commands 'R') - (countChar commands 'L')) ≥ m ∨ 
        ((countChar commands 'U') - (countChar commands 'D')) ≥ n) :
  solve_robot_safety n m commands = "unsafe" := sorry
-- </vc-theorems>