-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def name_that_number (n : Nat) : String := sorry

theorem name_that_number_string_properties {n : Nat} (h : n ≤ 99) :
  let result := name_that_number n
  result.length > 0 ∧ 
  result.all (fun c => c.isAlpha ∨ c = ' ') ∧
  result.all Char.isLower := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem name_that_number_deterministic {n : Nat} :
  name_that_number n = name_that_number n := sorry

theorem name_that_number_zero :
  name_that_number 0 = "zero" := sorry

theorem name_that_number_single_digit {n : Nat} (h₁ : n > 0) (h₂ : n ≤ 9) :
  let result := name_that_number n
  ¬ result.contains ' ' := sorry

theorem name_that_number_teens {n : Nat} (h₁ : n ≥ 10) (h₂ : n ≤ 19) :
  let result := name_that_number n
  (¬ result.contains ' ') ∧
  ((result.endsWith "teen") ∨ 
   result = "ten" ∨ 
   result = "eleven" ∨ 
   result = "twelve") := sorry

theorem name_that_number_two_digits {n : Nat} (h₁ : n ≥ 20) (h₂ : n ≤ 99) :
  let result := name_that_number n
  if n % 10 = 0 then
    ¬ result.contains ' '
  else
    (result.split (· = ' ')).length = 2 := sorry
-- </vc-theorems>