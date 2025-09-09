-- <vc-helpers>
-- </vc-helpers>

def minRoomsNeeded (n : Nat) (schedules : List String) : Nat := sorry

theorem min_rooms_bounds (n : Nat) (schedules : List String) :
  0 ≤ minRoomsNeeded n schedules ∧ minRoomsNeeded n schedules ≤ n := sorry

theorem min_rooms_concurrent (n : Nat) (schedules : List String) (day : Nat) (h : day < 7) :
  minRoomsNeeded n schedules ≥ (schedules.filter (fun sch => sch.data[day]? = some '1')).length := sorry

theorem min_rooms_empty (n : Nat) (schedules : List String) :
  (schedules.all (fun sch => List.all sch.data (· = '0'))) →
  minRoomsNeeded n schedules = 0 := sorry

theorem min_rooms_full_day (n : Nat) (schedules : List String) (day : Nat) (h : day < 7) :
  (schedules.all (fun sch => sch.data[day]? = some '1')) →
  minRoomsNeeded n schedules = n := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_rooms_needed 2 ["0101010", "1010101"]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_rooms_needed 3 ["0101011", "0011001", "0110111"]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_rooms_needed 1 ["1111111"]

-- Apps difficulty: competition
-- Assurance level: unguarded