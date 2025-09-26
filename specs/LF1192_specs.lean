-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_prodigy (n : Nat) : String := sorry 

theorem solve_prodigy_returns_valid_output {n : Nat} (h : n > 0) (h2 : n ≤ 10^8) :
  let result := solve_prodigy n
  (result = "lose") ∨ 
  (∃ m : Nat, result = "win " ++ toString m ∧ m > 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem small_inputs_always_win {n : Nat} (h : n > 0) (h2 : n ≤ 100) :
  ∃ m : Nat, solve_prodigy n = "win " ++ toString m := sorry

theorem large_inputs_always_lose {n : Nat} (h : n ≥ 10^7) (h2 : n ≤ 10^8) :
  solve_prodigy n = "lose" := sorry
-- </vc-theorems>