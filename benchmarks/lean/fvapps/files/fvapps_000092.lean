-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_time_to_send_presents (n m : Nat) (stack send_list : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identity_permutation_min_time {n : Nat} {stack : List Nat}
  (h1 : n > 0)
  (h2 : n ≤ 100000) 
  (h3 : stack.length = n)
  (h4 : ∀ x ∈ stack, 1 ≤ x ∧ x ≤ n)
  (h5 : stack.Nodup) :
  min_time_to_send_presents n n stack stack = n :=
sorry

theorem reverse_order_takes_longer {n : Nat} {stack : List Nat}
  (h1 : n > 0)
  (h2 : n ≤ 100000)
  (h3 : stack.length = n)
  (h4 : ∀ x ∈ stack, 1 ≤ x ∧ x ≤ n)
  (h5 : stack.Nodup) :
  min_time_to_send_presents n n stack stack.reverse ≥ min_time_to_send_presents n n stack stack :=
sorry
-- </vc-theorems>