-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_next_server (x y k : Nat) : String := sorry

theorem get_next_server_zero_scores (k : Nat) (h : k > 0) : 
  get_next_server 0 0 k = "Chef" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_next_server_valid_output (x y k : Nat) (h : k > 0) :
  get_next_server x y k = "Chef" ∨ get_next_server x y k = "Paja" := sorry

theorem get_next_server_alternates (x y k : Nat) (h : k > 0) :
  get_next_server (x + k) y k ≠ get_next_server x y k := sorry

theorem get_next_server_symmetrical (score k : Nat) (h : k > 0) :
  get_next_server score 0 k = get_next_server 0 score k := sorry
-- </vc-theorems>