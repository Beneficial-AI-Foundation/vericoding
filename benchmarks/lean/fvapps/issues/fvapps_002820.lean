-- <vc-preamble>
def sum_two_smallest_numbers (numbers : List Nat) : Nat :=
  sorry

def List.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + List.sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.minimum (l : List Nat) : Option Nat :=
  match l with
  | [] => none
  | x :: xs => some (List.foldl min x xs)
-- </vc-definitions>

-- <vc-theorems>
theorem sum_two_smallest_numbers_properties {numbers : List Nat} (h : numbers.length ≥ 2) :
  let result := sum_two_smallest_numbers numbers
  let sorted := numbers.toArray.qsort (·≤·)
  (result ≥ 0) ∧
  (match numbers.minimum with
   | none => true
   | some m => result ≥ 2 * m) ∧
  (result ≤ List.sum numbers) :=
  sorry

theorem sum_two_smallest_numbers_minimal {numbers : List Nat} (h : numbers.length ≥ 2) :
  let result := sum_two_smallest_numbers numbers
  ∀ i j, i < numbers.length → j < numbers.length → i ≠ j →
    result ≤ numbers[i]! + numbers[j]! :=
  sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval sum_two_smallest_numbers #[19, 5, 42, 2, 77]

/-
info: 3453455
-/
-- #guard_msgs in
-- #eval sum_two_smallest_numbers #[10, 343445353, 3453445, 3453545353453]

/-
info: 13
-/
-- #guard_msgs in
-- #eval sum_two_smallest_numbers #[5, 8, 12, 18, 22]
-- </vc-theorems>