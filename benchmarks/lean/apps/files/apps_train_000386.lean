-- <vc-helpers>
-- </vc-helpers>

def smallest_repunit_div_by_k (k : Nat) : Int := sorry

/- For any natural number k, smallest_repunit_div_by_k(k) is either -1 or between 1 and k inclusive -/

theorem output_range (k : Nat) :
  let result := smallest_repunit_div_by_k k
  result = -1 ∨ (1 ≤ result ∧ result ≤ k) :=
sorry

/- Certain numbers like 2,4,5,6,8,10 should return -1 as no repunit divides them -/

theorem invalid_inputs : 
  smallest_repunit_div_by_k 2 = -1 ∧
  smallest_repunit_div_by_k 4 = -1 ∧  
  smallest_repunit_div_by_k 5 = -1 ∧
  smallest_repunit_div_by_k 6 = -1 ∧
  smallest_repunit_div_by_k 8 = -1 ∧
  smallest_repunit_div_by_k 10 = -1 :=
sorry

/- If the result is not -1, then the repunit number of that length should be divisible by k -/

theorem result_divisibility (k : Nat) (result : Int) :
  smallest_repunit_div_by_k k = result →
  result ≠ -1 →
  ∃ repunit : Nat, repunit % k = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval smallest_repunit_div_by_k 1

/-
info: -1
-/
-- #guard_msgs in
-- #eval smallest_repunit_div_by_k 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval smallest_repunit_div_by_k 3

-- Apps difficulty: interview
-- Assurance level: guarded