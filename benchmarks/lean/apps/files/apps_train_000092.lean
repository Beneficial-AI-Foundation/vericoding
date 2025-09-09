-- <vc-helpers>
-- </vc-helpers>

def min_time_to_send_presents (n m : Nat) (stack send_list : List Nat) : Nat :=
sorry

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

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_time_to_send_presents 3 3 [3, 1, 2] [3, 2, 1]

/-
info: 8
-/
-- #guard_msgs in
-- #eval min_time_to_send_presents 7 2 [2, 1, 7, 3, 4, 5, 6] [3, 1]

-- Apps difficulty: interview
-- Assurance level: guarded