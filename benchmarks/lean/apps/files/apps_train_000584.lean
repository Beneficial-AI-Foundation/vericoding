-- <vc-helpers>
-- </vc-helpers>

def maxStadiumEvents (events : List (Nat × Nat)) : Nat := sorry

theorem maxStadiumEvents_non_negative (events : List (Nat × Nat)) :
  maxStadiumEvents events ≥ 0 := sorry

theorem maxStadiumEvents_bounded_by_input (events : List (Nat × Nat)) :
  maxStadiumEvents events ≤ events.length := sorry

theorem maxStadiumEvents_empty :
  maxStadiumEvents [] = 0 := sorry

theorem maxStadiumEvents_single_event (start duration : Nat) :
  maxStadiumEvents [(start, duration)] = 1 := sorry

theorem maxStadiumEvents_non_overlapping (events : List (Nat × Nat)) (h : events.length > 0) :
  (∀ i j, i < events.length → j < events.length → i ≠ j →
    ((events.get! i).1 + (events.get! i).2 ≤ (events.get! j).1) ∨ 
    ((events.get! j).1 + (events.get! j).2 ≤ (events.get! i).1)) →
  maxStadiumEvents events = events.length := sorry

theorem maxStadiumEvents_all_overlapping (events : List (Nat × Nat)) (h : events.length ≥ 2) :
  maxStadiumEvents (List.map (fun e => (0, e.2)) events) = 1 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_stadium_events [(2, 5), (9, 7), (15, 6), (9, 3)]

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_stadium_events [(1, 5)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_stadium_events [(1, 2), (4, 2), (7, 2)]

-- Apps difficulty: interview
-- Assurance level: guarded