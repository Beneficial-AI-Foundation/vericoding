def least_interval (tasks : List Char) (n : Nat) : Nat :=
  sorry

def countFrequencies (tasks : List Char) : List Nat :=
  sorry 

def maxFrequency (tasks : List Char) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def maxFrequencyCount (tasks : List Char) : Nat :=
  sorry

theorem least_interval_zero_cooldown (tasks : List Char) (h : tasks ≠ []) :
  least_interval tasks 0 = tasks.length :=
sorry

theorem least_interval_basic_properties (tasks : List Char) (n : Nat) (h : tasks ≠ []) :
  let result := least_interval tasks n
  let max_freq := maxFrequency tasks
  let max_freq_count := maxFrequencyCount tasks
  let min_possible := (max_freq - 1) * (n + 1) + max_freq_count
  result ≥ tasks.length ∧ result ≥ min_possible :=
sorry

theorem least_interval_upper_bound (tasks : List Char) (n : Nat) (h : tasks ≠ []) :
  least_interval tasks n ≤ tasks.length * (n + 1) :=
sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval least_interval ["A", "A", "A", "B", "B", "B"] 2

/-
info: 5
-/
-- #guard_msgs in
-- #eval least_interval ["A", "A", "A"] 1

/-
info: 4
-/
-- #guard_msgs in
-- #eval least_interval ["A", "B", "C", "D"] 0

-- Apps difficulty: interview
-- Assurance level: unguarded