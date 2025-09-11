-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fibonacci (n : Nat) : Nat := sorry

def memoized (f : α → β) : α → β := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fibonacci_matches_recursive (n : Nat) : 
  n ≤ 20 → 
  fibonacci n = match n with
    | 0 => 0
    | 1 => 1
    | n+2 => fibonacci (n+1) + fibonacci n
  := sorry

theorem fibonacci_recurrence (n : Nat) :
  n ≥ 2 → fibonacci n = fibonacci (n-1) + fibonacci (n-2) := sorry

theorem fibonacci_nonnegative (n : Nat) :
  fibonacci n ≥ 0 := sorry

theorem fibonacci_base_cases :
  fibonacci 0 = 0 ∧ fibonacci 1 = 1 := sorry

theorem fibonacci_monotonic (n : Nat) :
  n > 1 → fibonacci n ≥ fibonacci (n-1) := sorry

/-
info: 190392490709135
-/
-- #guard_msgs in
-- #eval fibonacci 70

/-
info: 1548008755920
-/
-- #guard_msgs in
-- #eval fibonacci 60

/-
info: 12586269025
-/
-- #guard_msgs in
-- #eval fibonacci 50
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible