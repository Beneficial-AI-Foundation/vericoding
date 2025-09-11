-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calcWeight (s : String) : Nat := sorry 

def orderWeight (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_input_gives_empty_output : orderWeight "" = "" := sorry

theorem output_has_same_elements (s : String) :
  s ≠ "" → 
  let input := s.split (· = ' ') |>.toArray
  let output := (orderWeight s).split (· = ' ') |>.toArray
  input.qsort (· ≤ ·) = output.qsort (· ≤ ·) := sorry

theorem weights_are_ordered (s : String) (i : Nat) :
  s ≠ "" →
  let result := (orderWeight s).split (· = ' ')
  i + 1 < result.length →
  let w1 := calcWeight (result.get! i)
  let w2 := calcWeight (result.get! (i+1))
  w1 ≤ w2 := sorry

theorem equal_weights_ordered_lexicographically (s : String) (i : Nat) :
  s ≠ "" →
  let result := (orderWeight s).split (· = ' ')
  i + 1 < result.length →
  let w1 := calcWeight (result.get! i)
  let w2 := calcWeight (result.get! (i+1))
  w1 = w2 → result.get! i ≤ result.get! (i+1) := sorry

theorem output_contains_only_digits (s : String) :
  s ≠ "" →
  let result := orderWeight s
  ∀ c ∈ result.data, c.isDigit ∨ c = ' ' := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval order_weight "103 123 4444 99 2000"

/-
info: expected2
-/
-- #guard_msgs in
-- #eval order_weight "56 65 74 100 99 68 86 180 90"

/-
info: expected3
-/
-- #guard_msgs in
-- #eval order_weight ""
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded