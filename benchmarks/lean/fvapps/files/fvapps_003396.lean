-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_positions (n : Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem positions_bound (n : Nat) : 
  let pos := get_positions n
  ∀ p ∈ pos, 0 ≤ p ∧ p ≤ 2 := 
  sorry

theorem positions_cycle (n rep : Nat) (h : 1 ≤ rep ∧ rep ≤ 3) :
  get_positions n = get_positions (n + 27 * rep) :=
  sorry
-- </vc-theorems>