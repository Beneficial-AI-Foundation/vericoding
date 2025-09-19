-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_non_negative (s : String) (k : Nat) :
  solve s k ≥ 0 :=
  sorry

theorem solve_bounded (s : String) (k : Nat) :
  let n := (s.split (· = ' ')).length
  solve s k ≤ n * (n-1) :=
  sorry
-- </vc-theorems>