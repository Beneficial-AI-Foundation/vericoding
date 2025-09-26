-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_zero_array (n : Nat) (arr : List Nat) : Bool := sorry

theorem single_element_array_always_true {arr : List Nat} (h : arr.length = 1) :
  can_zero_array 1 arr = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_elements_always_possible {n : Nat} {val : Nat} :
  let arr := List.replicate n val
  can_zero_array n arr = true := sorry

theorem scaling_preserves_result {n : Nat} {arr : List Nat} (scale : Nat) (h : scale > 0) (h2 : arr.length = n) :
  can_zero_array n arr = can_zero_array n (arr.map (· * scale)) := sorry

theorem all_zeros_after_first {n : Nat} {first : Nat} (h : first > 0) :
  let zeros := List.replicate (n-1) 0
  let arr := first :: zeros
  can_zero_array n arr = true := sorry
-- </vc-theorems>