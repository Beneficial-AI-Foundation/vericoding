-- <vc-helpers>
-- </vc-helpers>

def knight_rescue (N : List Nat) (x y : Nat) : Bool := sorry

theorem knight_rescue_same_parity (N : List Nat) (x y : Nat) (h : (x - y) % 2 = 0) :
  knight_rescue N x y = true := sorry

theorem knight_rescue_has_even (N : List Nat) (x y : Nat) 
  (h : ∃ n ∈ N, n % 2 = 0) :
  knight_rescue N x y = true := sorry

theorem knight_rescue_odd_diff_parity (N : List Nat) (x y : Nat)
  (h1 : (x - y) % 2 = 1)
  (h2 : ∀ n ∈ N, n % 2 = 1) :
  knight_rescue N x y = false := sorry

theorem knight_rescue_same_position (N : List Nat) (x : Nat) 
  (h : N.length > 0) :
  knight_rescue N x x = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval knight_rescue [2] 2 1

/-
info: True
-/
-- #guard_msgs in
-- #eval knight_rescue [1] 10 10

/-
info: False
-/
-- #guard_msgs in
-- #eval knight_rescue [1] 1 0

-- Apps difficulty: introductory
-- Assurance level: unguarded