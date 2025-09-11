-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_remainders (cases : List String) : List Nat := sorry

/- For any list of test cases, the length of results matches the input length -/
-- </vc-definitions>

-- <vc-theorems>
theorem find_remainders_length (cases : List String) : 
  (find_remainders cases).length = cases.length := sorry

/- Each remainder in the result is correctly computed -/

theorem find_remainders_correct (test_case : String) (a b : Nat) (h : test_case = s!"{a} {b}") :
  b > 0 → a > 0 → 
  find_remainders [test_case] = [a % b] := sorry

/- All remainders are non-negative and less than their divisors -/

theorem find_remainders_bounds (test_case : String) (a b : Nat) (h : test_case = s!"{a} {b}") :
  b > 0 → a > 0 →
  let r := (find_remainders [test_case]).head!
  0 ≤ r ∧ r < b := sorry

/- Division by one always yields zero remainder -/

theorem find_remainders_div_by_one (a : Nat) (h : a > 0) :
  find_remainders [s!"{a} 1"] = [0] := sorry

/-
info: [1, 100, 10]
-/
-- #guard_msgs in
-- #eval find_remainders ["1 2", "100 200", "40 15"]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval find_remainders ["7 3"]

/-
info: [0, 3]
-/
-- #guard_msgs in
-- #eval find_remainders ["10 2", "15 4"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded