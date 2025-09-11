-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 12
-/
-- #guard_msgs in
-- #eval min_notes_needed 1200

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_notes_needed 500

/-
info: 7
-/
-- #guard_msgs in
-- #eval min_notes_needed 242
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible