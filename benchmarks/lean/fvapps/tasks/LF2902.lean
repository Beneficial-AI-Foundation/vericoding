-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_of_n (n : Int) : List Int := sorry

theorem sum_of_n_length (n : Int) : (sum_of_n n).length = Int.natAbs n + 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_of_n_first_element (n : Int) : 
  (sum_of_n n).get! 0 = 0 := sorry

theorem sum_of_n_consecutive_diffs (n : Int) (i : Nat) 
  (h : i + 1 < (sum_of_n n).length) :
  (sum_of_n n).get! (i + 1) - (sum_of_n n).get! i = 
    if n < 0 
    then (-1 : Int) * (i + 1) 
    else i + 1 := sorry

theorem sum_of_n_signs (n : Int) (i : Nat) 
  (h1 : n ≠ 0)
  (h2 : i > 0) 
  (h3 : i < (sum_of_n n).length) :
  if n < 0 
  then (sum_of_n n).get! i ≤ 0
  else (sum_of_n n).get! i ≥ 0 := sorry

theorem sum_of_n_zero : 
  sum_of_n 0 = [0] := sorry
-- </vc-theorems>