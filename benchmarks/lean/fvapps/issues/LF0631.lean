-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_events (n k : Nat) (events : List Event) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_events_basic_properties {n k : Nat} {events : List Event}
  (h1 : n > 0)
  (h2 : k > 0)
  (h3 : n ≤ 100)
  (h4 : k ≤ 100)
  (h5 : ∀ e ∈ events, e.room ≥ 1 ∧ e.room ≤ k)
  (h6 : ∀ e ∈ events, e.start < e.stop)
  (h7 : ∀ e ∈ events, e.start ≤ 10^5-1)
  (h8 : ∀ e ∈ events, e.stop ≤ 10^5) :
  let result := solve_events n k events
  result ≥ 0 ∧ result ≤ events.length ∧ result ≤ n :=
  sorry

theorem solve_events_empty (n k : Nat)
  (h1 : n > 0)
  (h2 : k > 0)
  (h3 : n ≤ 100)
  (h4 : k ≤ 100) :
  solve_events n k [] = 0 :=
  sorry

theorem solve_events_single (n k start duration : Nat)
  (h1 : n > 0)
  (h2 : k > 0)
  (h3 : n ≤ 100)
  (h4 : k ≤ 100)
  (h5 : start > 0)
  (h6 : start ≤ 10^5-1)
  (h7 : duration > 0)
  (h8 : duration ≤ 100) :
  solve_events n k [{start := start, stop := start + duration, room := 1}] = 1 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_events 4 2 [[1, 10, 1], [10, 20, 2], [15, 50, 2], [20, 30, 2]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_events 2 1 [[1, 5, 1], [2, 3, 1]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_events 3 2 [[1, 2, 1], [2, 3, 1], [1, 3, 2]]
-- </vc-theorems>