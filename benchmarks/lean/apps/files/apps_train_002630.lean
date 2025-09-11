-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sol_equa (n : Nat) : List (List Nat) := sorry

/- The solutions to x² - 4y² = n are well-formed lists of pairs of natural numbers -/
-- </vc-definitions>

-- <vc-theorems>
theorem sol_equa_well_formed (n : Nat) :
  ∀ result : List (List Nat),
    result = sol_equa n →
    (∀ pair ∈ result, pair.length = 2) := sorry 

/- Each solution pair satisfies the equation x² - 4y² = n -/

theorem sol_equa_satisfies_equation (n : Nat) : 
  ∀ result : List (List Nat),
    result = sol_equa n →
    ∀ pair ∈ result,
      pair.get! 0 * pair.get! 0 - 4 * pair.get! 1 * pair.get! 1 = n := sorry

/- Solutions contain only positive x values and nonnegative y values -/

theorem sol_equa_positive_values (n : Nat) :
  ∀ result : List (List Nat),
    result = sol_equa n → 
    ∀ pair ∈ result,
      pair.get! 0 > 0 ∧ pair.get! 1 ≥ 0 := sorry

/- Solutions are ordered by descending x values -/

theorem sol_equa_ordered (n : Nat) :
  ∀ result : List (List Nat),
    result = sol_equa n →
    ∀ i < result.length - 1,
      (result.get! i).get! 0 > (result.get! (i+1)).get! 0 := sorry

/- For n = 90002, there are no solutions -/

theorem sol_equa_90002_empty :
  sol_equa 90002 = [] := sorry

/- For n = 5, there is exactly one solution: [[3,1]] -/

theorem sol_equa_5_single :
  sol_equa 5 = [[3,1]] := sorry

/-
info: [[3, 1]]
-/
-- #guard_msgs in
-- #eval sol_equa 5

/-
info: [[45003, 22501], [9003, 4499], [981, 467], [309, 37]]
-/
-- #guard_msgs in
-- #eval sol_equa 90005

/-
info: []
-/
-- #guard_msgs in
-- #eval sol_equa 90002
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded