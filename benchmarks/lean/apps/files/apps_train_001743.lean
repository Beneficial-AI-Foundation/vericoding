-- <vc-preamble>
def Time := String
deriving Inhabited

def alertNames (names : List String) (times : List Time) : List String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parseTime (t : Time) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem alertNames_output_ordered (names : List String) (times : List Time) :
  let result := alertNames names times
  ∀ i j, i < j → j < result.length → result[i]! ≤ result[j]! := by sorry

theorem alertNames_subset_of_input (names : List String) (times : List Time) :
  let result := alertNames names times
  ∀ x ∈ result, x ∈ names := by sorry

theorem alertNames_unique (names : List String) (times : List Time) :
  let result := alertNames names times
  List.Nodup result := by sorry

theorem alertNames_violation_exists (names : List String) (times : List Time) :
  let result := alertNames names times
  ∀ name ∈ result,
    let personTimes := (List.zip names times).filterMap 
      (fun p => if p.1 = name then some (parseTime p.2) else none)
    List.length personTimes ≥ 3 ∧
    ∃ t0 t1 t2, 
      t0 ∈ personTimes ∧ 
      t1 ∈ personTimes ∧
      t2 ∈ personTimes ∧
      t0 < t1 ∧ t1 < t2 ∧
      t2 - t0 ≤ 100 := by sorry

theorem alertNames_short_inputs (names : List String) (times : List Time) :
  List.length names ≤ 2 → alertNames names times = [] := by sorry

/-
info: ['daniel']
-/
-- #guard_msgs in
-- #eval alert_names ["daniel", "daniel", "daniel", "luis", "luis", "luis", "luis"] ["10:00", "10:40", "11:00", "09:00", "11:00", "13:00", "15:00"]

/-
info: ['bob']
-/
-- #guard_msgs in
-- #eval alert_names ["alice", "alice", "alice", "bob", "bob", "bob", "bob"] ["12:01", "12:00", "18:00", "21:00", "21:20", "21:30", "23:00"]

/-
info: ['clare', 'leslie']
-/
-- #guard_msgs in
-- #eval alert_names ["leslie", "leslie", "leslie", "clare", "clare", "clare", "clare"] ["13:00", "13:20", "14:00", "18:00", "18:51", "19:30", "19:49"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded