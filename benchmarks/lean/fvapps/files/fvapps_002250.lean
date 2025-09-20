-- <vc-preamble>
abbrev M : Nat := 1000000007

def list_sum : List Nat → Nat
  | [] => 0
  | x::xs => x + list_sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_sequence_sum (n m : Nat) (sequence : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_sequence_sum_nonneg (n m : Nat) (sequence : List Nat) :
  solve_sequence_sum n m sequence ≥ 0 :=
sorry

theorem solve_sequence_sum_special_case :
  solve_sequence_sum 1 1 [0] = 2 :=
sorry
-- </vc-theorems>