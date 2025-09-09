-- <vc-helpers>
-- </vc-helpers>

def create_phone_number (numbers: List Nat) : String := sorry

theorem phone_number_format (numbers: List Nat) 
  (h1: numbers.length = 10)
  (h2: ∀ n ∈ numbers, n ≤ 9) :
  let result := create_phone_number numbers;
  result.length = 14 ∧ 
  result = s!"({numbers[0]}{numbers[1]}{numbers[2]}) {numbers[3]}{numbers[4]}{numbers[5]}-{numbers[6]}{numbers[7]}{numbers[8]}{numbers[9]}" := sorry

theorem phone_number_matches_input (numbers: List Nat)
  (h1: numbers.length = 10)
  (h2: ∀ n ∈ numbers, n ≤ 9) :
  let result := create_phone_number numbers;
  let digits := result.toList.filter Char.isDigit;
  digits.map (λ c => c.toString.toNat!) = numbers := sorry

theorem phone_number_type (numbers: List Nat)
  (h1: numbers.length = 10)
  (h2: ∀ n ∈ numbers, n ≤ 9) :
  let result := create_phone_number numbers;
  result.data.length > 0 := sorry

/-
info: '(123) 456-7890'
-/
-- #guard_msgs in
-- #eval create_phone_number [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]

/-
info: '(111) 111-1111'
-/
-- #guard_msgs in
-- #eval create_phone_number [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-
info: '(000) 000-0000'
-/
-- #guard_msgs in
-- #eval create_phone_number [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

-- Apps difficulty: introductory
-- Assurance level: unguarded