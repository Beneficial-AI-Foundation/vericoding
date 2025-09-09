-- <vc-helpers>
-- </vc-helpers>

def find_poisoned_duration (time_series : List Int) (duration : Int) : Int := sorry

theorem poisoned_duration_properties
  (time_series : List Int) 
  (duration : Int)
  (h1 : duration > 0) :
  let result := find_poisoned_duration time_series duration
  -- Result is non-negative
  (result ≥ 0) ∧ 
  -- Empty list returns 0
  (time_series = [] → result = 0) ∧
  -- Result bounded by total duration span plus duration
  (time_series ≠ [] → 
    result ≤ (List.getD time_series (time_series.length - 1) 0 - 
              List.getD time_series 0 0) + duration) ∧
  -- Consecutive times within duration bound the result
  (∀ i, i < time_series.length - 1 →
    List.getD time_series (i+1) 0 - List.getD time_series i 0 < duration →
    List.getD time_series (i+1) 0 - List.getD time_series i 0 ≤ result) := sorry

theorem duration_monotonicity
  (time_series : List Int) :
  find_poisoned_duration time_series 1 ≤ find_poisoned_duration time_series 2 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_poisoned_duration [1, 4] 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_poisoned_duration [1, 2] 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_poisoned_duration [] 5

-- Apps difficulty: interview
-- Assurance level: guarded