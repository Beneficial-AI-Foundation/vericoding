-- <vc-preamble>
def countChanges (arr : List Nat) : Nat :=
  let indices := List.range (arr.length - 1)
  indices.foldl (fun acc i =>
    if h : i < arr.length ∧ i + 1 < arr.length then
      if arr[i]'h.left ≠ arr[i+1]'h.right then
        acc + 1
      else acc
    else acc) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_sequence (arr : List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_sequence_non_negative (arr : List Nat) :
  ∀ x ∈ find_sequence arr, x ≥ 0 :=
sorry

theorem find_sequence_trailing_zero (arr : List Nat) :
  arr.length > 0 → arr.getLast! = 0 →
  (find_sequence arr).getLast! = 0 :=
sorry

theorem find_sequence_run_lengths (arr : List Nat) (pos : Nat) (h : pos < arr.length) :
  let val := arr[pos]'h
  let run_length := (find_sequence arr).get! pos
  ∃ actual_count : Nat,
    (∀ i, pos ≤ i ∧ i < pos + actual_count →
      ∃ h' : i < arr.length, arr[i]'h' = val) ∧
    (val = 0 ∧ pos + actual_count = arr.length → run_length = 0) ∧
    (¬(val = 0 ∧ pos + actual_count = arr.length) → run_length = actual_count) :=
sorry

theorem find_sequence_length (arr : List Nat) :
  arr.length > 0 →
  (find_sequence arr).length = 1 + countChanges arr :=
sorry
-- </vc-theorems>