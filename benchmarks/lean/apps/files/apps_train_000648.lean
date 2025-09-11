-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_latest_bus (n : Nat) (d : Nat) (buses : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_latest_bus_single_bus
    (d : Nat) (h1 : d > 0) (h2 : d ≤ 1000) :
    solve_latest_bus 1 d [1] = d :=
sorry

theorem solve_latest_bus_identical_buses
    (d bus : Nat) (h1 : d > 0) (h2 : d ≤ 100) 
    (h3 : bus > 0) (h4 : bus ≤ 10) :
    let result := solve_latest_bus 5 d (List.replicate 5 bus)
    result ≤ d ∧ result % bus = 0 :=
sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_latest_bus 3 10 [3, 7, 2]

/-
info: 99
-/
-- #guard_msgs in
-- #eval solve_latest_bus 4 100 [11, 10, 5, 50]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_latest_bus 1 1 [1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible