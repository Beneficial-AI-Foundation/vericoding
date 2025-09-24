-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def monkey_count (n : Nat) : List Nat := sorry

theorem monkey_count_length {n : Nat} (h : n > 0) : 
  (monkey_count n).length = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem monkey_count_first {n : Nat} (h : n > 0) :
  (monkey_count n).head! = 1 := sorry 

theorem monkey_count_last {n : Nat} (h : n > 0) :
  (monkey_count n).getLast! = n := sorry
-- </vc-theorems>