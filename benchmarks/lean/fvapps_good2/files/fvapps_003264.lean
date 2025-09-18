-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def next_higher (start_value k : Nat) : Nat :=
sorry

def sum_part (n : Nat) : Nat :=
sorry

def qualified : Nat → List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_part_properties {n : Nat} (hn : n > 0 ∧ n ≤ 1000) :
  sum_part n ≥ n :=
sorry
-- </vc-theorems>