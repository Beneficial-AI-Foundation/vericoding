def next_higher (start_value k : Nat) : Nat := sorry 

def sum_part (n : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def qualified : Nat → List Nat := sorry

theorem sum_part_properties {n : Nat} (hn : n > 0 ∧ n ≤ 1000) :
  sum_part n ≥ n := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible