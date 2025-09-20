-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_sequence (a b n : Nat) : Nat :=
sorry

def bitXor (a b : Nat) : Nat :=
sorry

def bitNot (a : Nat) : Nat :=
sorry

def bitLength (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_sequence_nonnegative (a b n : Nat) :
  n > 0 → n ≤ 3 → solve_sequence a b n ≥ 0 :=
sorry

theorem solve_sequence_first (a b : Nat) :
  solve_sequence a b 1 = a :=
sorry

theorem solve_sequence_second (a b : Nat) :
  solve_sequence a b 2 = b :=
sorry

theorem solve_sequence_symmetric (a b : Nat) :
  solve_sequence a b 3 = solve_sequence b a 3 :=
sorry
-- </vc-theorems>