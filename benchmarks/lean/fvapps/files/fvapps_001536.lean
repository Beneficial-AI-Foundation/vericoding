-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_notes_needed (amount : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_notes_needed_nonnegative (amount : Nat) : 
  min_notes_needed amount ≥ 0 :=
  sorry

theorem min_notes_needed_exact_change (amount : Nat) :
  let notes := [100, 50, 10, 5, 2, 1]
  let count := min_notes_needed amount
  let remainingAndCount := notes.foldl 
    (fun (acc : Nat × Nat) (note : Nat) => 
      let remaining := acc.1
      let count := acc.2
      let notes_used := remaining / note
      (remaining - notes_used * note, count + notes_used))
    (amount, 0)
  count = remainingAndCount.2 ∧ remainingAndCount.1 = 0 :=
  sorry
-- </vc-theorems>