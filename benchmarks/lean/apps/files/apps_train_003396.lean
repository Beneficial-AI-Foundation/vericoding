-- <vc-helpers>
-- </vc-helpers>

def get_positions (n : Nat) : List Nat :=
  sorry

theorem positions_bound (n : Nat) : 
  let pos := get_positions n
  ∀ p ∈ pos, 0 ≤ p ∧ p ≤ 2 := 
  sorry

theorem positions_cycle (n rep : Nat) (h : 1 ≤ rep ∧ rep ≤ 3) :
  get_positions n = get_positions (n + 27 * rep) :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible