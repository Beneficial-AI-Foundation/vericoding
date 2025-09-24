-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) : Nat := sorry 

theorem solve_non_negative (n : Nat) :
  solve n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_linear_pattern (n : Nat) :
  n ≥ 12 → solve n = 292 + 49 * (n - 11) := sorry

theorem solve_initial_sequence (n : Nat) :
  n < 12 → solve n = match n with
    | 0 => 0
    | 1 => 4  
    | 2 => 10
    | 3 => 20
    | 4 => 35
    | 5 => 56
    | 6 => 83
    | 7 => 116
    | 8 => 155
    | 9 => 198
    | 10 => 244
    | 11 => 292
    | _ => 0 := sorry

theorem solve_strictly_increasing {n : Nat} :
  n > 0 → solve n > solve (n-1) := sorry
-- </vc-theorems>