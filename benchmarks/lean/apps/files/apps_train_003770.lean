-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat := sorry

def find_next_square (n : Nat) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem next_square_of_perfect (n : Nat) (h : ∃ k, n = k * k) : 
  find_next_square n = ((sqrt n + 1) * (sqrt n + 1)) := sorry

theorem non_square_returns_minus_one (n : Nat) (h : ¬∃ k, n = k * k) :
  find_next_square n = -1 := sorry

/-
info: 144
-/
-- #guard_msgs in
-- #eval find_next_square 121

/-
info: 676
-/
-- #guard_msgs in
-- #eval find_next_square 625

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_next_square 155
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded