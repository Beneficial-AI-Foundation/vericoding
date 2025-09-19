-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lockerRun (n : Nat) : List Nat := sorry

theorem locker_run_returns_positive (n : Nat) :
  ∀ x ∈ lockerRun n, x > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem locker_run_returns_perfect_squares (n : Nat) :
  ∀ x ∈ lockerRun n, ∃ k : Nat, k * k = x := sorry

theorem locker_run_bounded_by_input (n : Nat) :
  ∀ x ∈ lockerRun n, x ≤ n := sorry

theorem locker_run_ascending (n : Nat) (i j : Nat) (h1 : i < j) 
    (h2 : i < (lockerRun n).length) (h3 : j < (lockerRun n).length) :
  (lockerRun n)[i]'h2 ≤ (lockerRun n)[j]'h3 := sorry

theorem locker_run_length (n : Nat) :
  ∃ k : Nat, k * k ≤ n ∧ (k + 1) * (k + 1) > n ∧ (lockerRun n).length = k := sorry

theorem locker_run_monotone (n₁ n₂ : Nat) : 
  (lockerRun n₁).length ≤ (lockerRun (n₁ + n₂)).length := sorry

theorem locker_run_subset (n₁ n₂ : Nat) :
  ∀ x ∈ lockerRun n₁, x ∈ lockerRun (n₁ + n₂) := sorry
-- </vc-theorems>