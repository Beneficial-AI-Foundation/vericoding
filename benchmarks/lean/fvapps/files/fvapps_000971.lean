-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_panipuri_speed (n : Nat) (eating_times : List Nat) : Nat := sorry

theorem solve_panipuri_speed_returns_positive (n : Nat) (eating_times : List Nat)
    (h1 : n > 0)
    (h2 : eating_times.length > 0)
    (h3 : ∀ x ∈ eating_times, x > 0) :
    solve_panipuri_speed n eating_times > 0 := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_panipuri_speed_returns_natural (n : Nat) (eating_times : List Nat)
    (h1 : n > 0)
    (h2 : eating_times.length > 0)
    (h3 : ∀ x ∈ eating_times, x > 0) :
    ∃ k : Nat, solve_panipuri_speed n eating_times = k := by sorry

theorem solve_panipuri_speed_minimum (n : Nat) (eating_times : List Nat)
    (h1 : n > 0)
    (h2 : eating_times.length > 0)
    (h3 : ∀ x ∈ eating_times, x > 0) :
    ∃ min : Nat, (∀ x ∈ eating_times, min ≤ x) ∧ solve_panipuri_speed n eating_times ≥ n / min := by sorry

theorem solve_panipuri_speed_single_customer (eating_times : List Nat)
    (h1 : eating_times.length > 0)
    (h2 : ∀ x ∈ eating_times, x > 0) :
    ∃ min : Nat, (∀ x ∈ eating_times, min ≤ x) ∧ solve_panipuri_speed 1 eating_times = (1 + min - 1) / min := by sorry

theorem solve_panipuri_speed_single_time :
    solve_panipuri_speed 1 [1] = 1 := by sorry

theorem solve_panipuri_speed_single_customer_time_two :
    solve_panipuri_speed 1 [2] = 1 := by sorry

theorem solve_panipuri_speed_equal_times :
    solve_panipuri_speed 3 [2, 2, 2] = 2 := by sorry
-- </vc-theorems>