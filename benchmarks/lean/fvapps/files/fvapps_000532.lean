-- <vc-preamble>
def count_ball_bounces (n: Nat) : Nat := sorry

def isPowerOfTwo (n: Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def allOnesInBinary (n: Nat) : Bool := sorry 

def countOnesInBinary (n: Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_negative_result (distance : Nat) :
  count_ball_bounces distance ≥ 0 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_ball_bounces 13

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_ball_bounces 7

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_ball_bounces 16
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible