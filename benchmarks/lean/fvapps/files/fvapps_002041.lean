-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minRoomsNeeded (n : Nat) (schedules : List String) : Nat := sorry

theorem min_rooms_bounds (n : Nat) (schedules : List String) :
  0 ≤ minRoomsNeeded n schedules ∧ minRoomsNeeded n schedules ≤ n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_rooms_concurrent (n : Nat) (schedules : List String) (day : Nat) (h : day < 7) :
  minRoomsNeeded n schedules ≥ (schedules.filter (fun sch => sch.data[day]? = some '1')).length := sorry

theorem min_rooms_empty (n : Nat) (schedules : List String) :
  (schedules.all (fun sch => List.all sch.data (· = '0'))) →
  minRoomsNeeded n schedules = 0 := sorry

theorem min_rooms_full_day (n : Nat) (schedules : List String) (day : Nat) (h : day < 7) :
  (schedules.all (fun sch => sch.data[day]? = some '1')) →
  minRoomsNeeded n schedules = n := sorry
-- </vc-theorems>