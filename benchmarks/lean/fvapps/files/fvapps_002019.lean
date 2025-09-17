-- <vc-preamble>
def min_steps_to_lift (n : Nat) (weights : List Nat) : Nat := sorry

theorem min_steps_nonneg (n : Nat) (weights : List Nat) : 
  min_steps_to_lift n weights ≥ 0 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_odd_frequencies (weights : List Nat) : Nat :=
  let freqs := weights.foldl (fun acc x => 
    match acc.find? (fun p => p.1 = x) with
    | some p => acc.erase p ++ [(p.1, p.2 + 1)]
    | none => acc ++ [(x, 1)]
    ) []
  (freqs.filter (fun p => p.2 % 2 = 1)).length
-- </vc-definitions>

-- <vc-theorems>
theorem min_steps_upper_bound (n : Nat) (weights : List Nat) :
  min_steps_to_lift n weights ≤ n := sorry

theorem min_steps_odd_freq_bound (n : Nat) (weights : List Nat) :
  min_steps_to_lift n weights ≥ count_odd_frequencies weights := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_steps_to_lift 5 [1, 1, 2, 3, 3]

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_steps_to_lift 4 [0, 1, 2, 3]

/-
info: 11
-/
-- #guard_msgs in
-- #eval min_steps_to_lift 13 [92, 194, 580495, 0, 10855, 41704, 13, 96429, 33, 213, 0, 92, 140599]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded