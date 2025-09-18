-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>