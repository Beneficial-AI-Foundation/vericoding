-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc' (s : String) : Nat :=
match s with
| _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_non_negative (s : String) : 
  calc' s ≥ 0 := by
  sorry

theorem calc_empty_string :
  calc' "" = 0 := by
  sorry 

theorem calc_is_sum_of_seven_differences (s : String) :
  calc' s = ((String.join (List.map toString (List.map Char.toNat (String.toList s)))).toList.filter (· = '7')).length * 6 := by
  sorry

theorem calc_bounded_by_string_length (s : String) (h : s ≠ "") :
  calc' s ≤ (String.join (List.map toString (List.map Char.toNat (String.toList s)))).length * 6 := by
  sorry

end Example

/-
info: 6
-/
-- #guard_msgs in
-- #eval calc "ABC"

/-
info: 12
-/
-- #guard_msgs in
-- #eval calc "jaam"

/-
info: 30
-/
-- #guard_msgs in
-- #eval calc "aaaaaddddr"
-- </vc-theorems>