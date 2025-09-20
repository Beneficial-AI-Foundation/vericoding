-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_robot_exits (N M : Nat) (robots exits : List Nat) : Nat := sorry

theorem basic_case_2x2 :
  solve_robot_exits 2 2 [2, 3] [1, 4] = 3 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem basic_case_3x4 :
  solve_robot_exits 3 4 [2, 5, 10] [1, 3, 7, 13] = 8 := sorry

theorem simple_case_1x2 :
  solve_robot_exits 1 2 [2] [1, 3] = 2 := sorry

theorem solve_robot_exits_spec {N M : Nat} {robots exits : List Nat}
  (h1 : N > 0)
  (h2 : M > 0) 
  (h3 : ∀ r ∈ robots, r ≤ N * M)
  (h4 : ∀ e ∈ exits, e ≤ N * M) :
  solve_robot_exits N M robots exits ≥ 0 := sorry
-- </vc-theorems>