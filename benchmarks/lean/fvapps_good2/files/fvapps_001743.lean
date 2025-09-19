-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Time := String
deriving Inhabited

def alertNames (names : List String) (times : List Time) : List String :=
  sorry

def parseTime (t : Time) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem alertNames_output_ordered (names : List String) (times : List Time) :
  let result := alertNames names times
  ∀ i j, i < j → j < result.length → result[i]! ≤ result[j]! := by
sorry

theorem alertNames_subset_of_input (names : List String) (times : List Time) :
  let result := alertNames names times
  ∀ x ∈ result, x ∈ names := by
sorry

theorem alertNames_unique (names : List String) (times : List Time) :
  let result := alertNames names times
  List.Nodup result := by
sorry

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
      t2 - t0 ≤ 100 := by
sorry

theorem alertNames_short_inputs (names : List String) (times : List Time) :
  List.length names ≤ 2 → alertNames names times = [] := by
sorry
-- </vc-theorems>