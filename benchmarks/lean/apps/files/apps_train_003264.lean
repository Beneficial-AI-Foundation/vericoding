-- <vc-preamble>
def next_higher (start_value k : Nat) : Nat := sorry 

def sum_part (n : Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def qualified : Nat → List Nat := sorry

theorem sum_part_properties {n : Nat} (hn : n > 0 ∧ n ≤ 1000) :
  sum_part n ≥ n := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible