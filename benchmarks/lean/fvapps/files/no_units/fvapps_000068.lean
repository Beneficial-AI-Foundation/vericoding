-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cost_clear_mines (a b : Nat) (mine_map : String) : Nat := sorry 

theorem min_cost_non_negative (a b : Nat) (mine_map : String) :
  min_cost_clear_mines a b mine_map ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mines_exist_min_cost (a b : Nat) (mine_map : String) :
  (∃ c, c ∈ mine_map.data ∧ c = '1') →
  min_cost_clear_mines a b mine_map ≥ a := sorry

theorem cost_upper_bound (a b : Nat) (mine_map : String) :
  min_cost_clear_mines a b mine_map ≤ a * (mine_map.data.filter (· = '1')).length := sorry

theorem single_mine_cost (a b : Nat) :
  min_cost_clear_mines a b "1" = a := sorry

theorem single_mine_cost_with_gap (a b : Nat) :
  min_cost_clear_mines a b "010" = a := sorry

theorem new_activation_cheaper :
  min_cost_clear_mines 2 3 "101" = 4 := sorry
-- </vc-theorems>