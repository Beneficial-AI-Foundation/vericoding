-- <vc-helpers>
-- </vc-helpers>

def get_next_server (x y k : Nat) : String := sorry

theorem get_next_server_zero_scores (k : Nat) (h : k > 0) : 
  get_next_server 0 0 k = "Chef" := sorry

theorem get_next_server_valid_output (x y k : Nat) (h : k > 0) :
  get_next_server x y k = "Chef" ∨ get_next_server x y k = "Paja" := sorry

theorem get_next_server_alternates (x y k : Nat) (h : k > 0) :
  get_next_server (x + k) y k ≠ get_next_server x y k := sorry

theorem get_next_server_symmetrical (score k : Nat) (h : k > 0) :
  get_next_server score 0 k = get_next_server 0 score k := sorry

/-
info: 'Paja'
-/
-- #guard_msgs in
-- #eval get_next_server 1 3 3

/-
info: 'Chef'
-/
-- #guard_msgs in
-- #eval get_next_server 5 7 2

/-
info: 'Paja'
-/
-- #guard_msgs in
-- #eval get_next_server 38657 76322 564

-- Apps difficulty: interview
-- Assurance level: unguarded