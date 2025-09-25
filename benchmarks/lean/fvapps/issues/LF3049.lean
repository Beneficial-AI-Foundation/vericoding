-- <vc-preamble>
def List.maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => List.foldl Nat.max h t

def List.sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => h + List.sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def queue_time (customers : List Nat) (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem queue_time_non_negative (customers : List Nat) (n : Nat) (h : n > 0) :
  queue_time customers n ≥ 0 :=
  sorry 

theorem queue_time_empty_list (n : Nat) (h : n > 0) :
  queue_time [] n = 0 :=
  sorry

theorem queue_time_monotonic (customers : List Nat) (n : Nat) (h : n > 0) :
  queue_time customers (n + 1) ≤ queue_time customers n :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval queue_time [] 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval queue_time [2] 5

/-
info: 9
-/
-- #guard_msgs in
-- #eval queue_time [2, 2, 3, 3, 4, 4] 2
-- </vc-theorems>