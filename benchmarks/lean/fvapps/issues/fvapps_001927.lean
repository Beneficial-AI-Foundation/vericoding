-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_lucky_permutation (n : Nat) : Option (List Nat) := sorry

theorem length_property {n : Nat} {result : List Nat} 
  (h : find_lucky_permutation n = some result) : 
    result.length = n ∧ 
    (∃ m, result.minimum? = some m ∧ m = 1) ∧
    (∃ m, result.maximum? = some m ∧ m = n) ∧
    (∀ x ∈ result, ∀ y ∈ result, x = y → result.find? (·= x) = result.find? (·= y)) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem negative_cases :
  find_lucky_permutation 2 = none ∧ 
  find_lucky_permutation 3 = none ∧
  find_lucky_permutation 6 = none ∧
  find_lucky_permutation 7 = none := sorry

theorem small_valid_cases :
  find_lucky_permutation 1 = some [1] ∧
  (∃ result, find_lucky_permutation 4 = some result ∧ 
    result.length = 4 ∧
    (∃ l, l = [1,2,3,4] ∧ ∀ x ∈ result, x ∈ l)) := sorry

theorem divisibility_rule {n : Nat} 
  (h : n % 4 > 1) :
  find_lucky_permutation n = none := sorry

/-
info: [1]
-/
-- #guard_msgs in
-- #eval find_lucky_permutation 1

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_lucky_permutation 2

/-
info: [2, 4, 1, 3]
-/
-- #guard_msgs in
-- #eval find_lucky_permutation 4
-- </vc-theorems>