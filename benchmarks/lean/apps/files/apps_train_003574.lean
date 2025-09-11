-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arbitrate (s : String) (n : Nat) : String := sorry

theorem arbitrate_all_zeros (n : Nat) (h : 0 < n) :
  arbitrate (String.mk (List.replicate n '0')) n = String.mk (List.replicate n '0') := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arbitrate_single_one (n i : Nat) (h1 : 0 < n) (h2 : i < n) :
  arbitrate (String.mk (List.replicate i '0' ++ '1' :: List.replicate (n - i - 1) '0')) n = 
  String.mk (List.replicate i '0' ++ '1' :: List.replicate (n - i - 1) '0') := sorry

theorem arbitrate_single_one_count (n i : Nat) (h1 : 0 < n) (h2 : i < n) :
  ((arbitrate (String.mk (List.replicate i '0' ++ '1' :: List.replicate (n - i - 1) '0')) n).data.filter (· = '1')).length = 1 := sorry

theorem arbitrate_all_ones (n : Nat) (h : 0 < n) :
  arbitrate (String.mk (List.replicate n '1')) n = 
  String.mk ('1' :: List.replicate (n - 1) '0') := sorry

/-
info: '001000000'
-/
-- #guard_msgs in
-- #eval arbitrate "001000101" 9

/-
info: '000000100'
-/
-- #guard_msgs in
-- #eval arbitrate "000000101" 9

/-
info: '0000'
-/
-- #guard_msgs in
-- #eval arbitrate "0000" 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded