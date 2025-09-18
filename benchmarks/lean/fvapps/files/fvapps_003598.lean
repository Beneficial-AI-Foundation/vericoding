-- <vc-preamble>
def moment_of_time_in_space (s : String) : List Bool :=
  sorry

def sum_digits (s : String) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_non_digits (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_three_bools (s : String) :
  let result := moment_of_time_in_space s
  List.length result = 3 ∧ 
  List.all result (fun x => x = true ∨ x = false) :=
  sorry

theorem exactly_one_true (s : String) :
  let result := moment_of_time_in_space s 
  let count := List.foldl (fun acc b => acc + if b then 1 else 0) 0 result
  count = 1 :=
  sorry

theorem time_space_comparison (s : String) :
  let time := sum_digits s
  let space := count_non_digits s
  let result := moment_of_time_in_space s
  (time < space → result = [true, false, false]) ∧
  (time = space → result = [false, true, false]) ∧ 
  (time > space → result = [false, false, true]) :=
  sorry

theorem permutation_invariant {s₁ s₂ : String} :
  s₁.length = s₂.length →
  (∀ c, s₁.find (· = c) = s₂.find (· = c)) →
  moment_of_time_in_space s₁ = moment_of_time_in_space s₂ :=
  sorry

/-
info: [True, False, False]
-/
-- #guard_msgs in
-- #eval moment_of_time_in_space "01:00 pm"

/-
info: [False, True, False]
-/
-- #guard_msgs in
-- #eval moment_of_time_in_space "12:02 pm"

/-
info: [False, False, True]
-/
-- #guard_msgs in
-- #eval moment_of_time_in_space "12:30 pm"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded