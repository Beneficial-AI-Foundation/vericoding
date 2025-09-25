-- <vc-preamble>
def length {α : Type} : Node α → Nat
  | Node.nil => 0
  | Node.cons _ next => 1 + length next
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count {α : Type} [BEq α] : Node α → α → Nat 
  | Node.nil, _ => 0
  | Node.cons x next, val => 
    let rest := count next val
    if x == val then 1 + rest else rest
-- </vc-definitions>

-- <vc-theorems>
theorem length_equals_list_length {α : Type} (xs : List α) :
  length (xs.foldl (fun acc x => Node.cons x acc) Node.nil) = xs.length :=
sorry

theorem count_equals_list_count {α : Type} [BEq α] (xs : List α) (val : α) :
  count (xs.foldl (fun acc x => Node.cons x acc) Node.nil) val = xs.count val :=
sorry 

theorem count_none_is_zero {α : Type} [BEq α] (node : Node α) (default : α) :
  count node default = 0 :=
sorry

theorem count_leq_length {α : Type} [BEq α] (node : Node α) (val : α) :
  count node val ≤ length node :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval length None

/-
info: 0
-/
-- #guard_msgs in
-- #eval count None 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval length Node(1)

/-
info: 1
-/
-- #guard_msgs in
-- #eval count node 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval count node 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval length test_list_one_two_three()

/-
info: 1
-/
-- #guard_msgs in
-- #eval count list123 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval count list123 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval count list123 4
-- </vc-theorems>