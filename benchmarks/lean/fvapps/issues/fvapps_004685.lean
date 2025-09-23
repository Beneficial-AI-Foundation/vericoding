-- <vc-preamble>
def sumOfIntegersInString (s : String) : Nat :=
  sorry

def sumOfMatchedNumbers (s : String) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + List.sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem sum_matches_individual_numbers (s : String) : 
  sumOfIntegersInString s = sumOfMatchedNumbers s := by 
  sorry

theorem single_number_returns_itself (n : Nat) :
  sumOfIntegersInString (toString n) = n := by 
  sorry

theorem space_separated_sum (nums : List Nat) :
  sumOfIntegersInString (String.intercalate " " (nums.map toString)) = List.sum nums := by
  sorry

theorem output_is_nonnegative (s : String) :
  sumOfIntegersInString s ≥ 0 := by
  sorry

/-
info: 3635
-/
-- #guard_msgs in
-- #eval sum_of_integers_in_string "The30quick20brown10f0x1203jumps914ov3r1349the102l4zy dog"

/-
info: 12
-/
-- #guard_msgs in
-- #eval sum_of_integers_in_string "12"

/-
info: 3
-/
-- #guard_msgs in
-- #eval sum_of_integers_in_string "h3llo w0rld"
-- </vc-theorems>