-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_chocolate_break_cost (n m k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_cost_for_exact_pieces (n m k : Nat)
  (hn : n > 0) (hm : m > 0) (hk : k ≤ 25)
  (h_exact : n * m = k) :
  find_min_chocolate_break_cost n m k = 0 :=
sorry 

theorem zero_pieces_cost_nothing (n m k : Nat)
  (hn : n > 0) (hm : m > 0)
  (hk_zero : k = 0) :
  find_min_chocolate_break_cost n m k = 0 :=
sorry
-- </vc-theorems>