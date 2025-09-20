-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def balanced_num (n : Nat) : String := sorry

theorem balanced_num_valid_output (n : Nat) : 
  balanced_num n = "Balanced" ∨ balanced_num n = "Not Balanced" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem small_nums_balanced (n : Nat) :
  n < 100 → balanced_num n = "Balanced" := sorry

theorem balanced_equals_digit_sums_eq (n : Nat) (s : String) :
  s = toString n →
  s.length ≥ 3 →
  let left_idx := (s.length - 1) / 2
  let right_start := if s.length % 2 = 0 then left_idx else left_idx
  let left_sum := (s.take left_idx).toList.map Char.toNat |>.foldl (·+·) 0
  let right_sum := (s.drop right_start).toList.map Char.toNat |>.foldl (·+·) 0
  balanced_num n = "Balanced" ↔ left_sum = right_sum := sorry

theorem mirrored_nums_balanced (d1 d2 : Nat) :
  d1 < 10 →
  d2 < 10 →
  balanced_num (d1 * 100 + d2 * 10 + d1) = "Balanced" ∧ 
  balanced_num (d1 * 1000 + d2 * 100 + d2 * 10 + d1) = "Balanced" := sorry
-- </vc-theorems>