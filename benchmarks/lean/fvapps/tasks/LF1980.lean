-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_array_operations (n : Nat) (arr : List Int) : List (Nat × Nat × List Int) :=
sorry

def verify_operations (n : Nat) (arr : List Int) (ops : List (Nat × Nat × List Int)) : Bool :=
sorry

def valid_operation (n : Nat) (op : Nat × Nat × List Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_array_operations_properties
  (n : Nat) (arr : List Int) (h : 0 < n) (h2 : n ≤ 100) :
  let ops := solve_array_operations n arr
  List.length ops = 3 ∧
  (∀ op ∈ ops, valid_operation n op) ∧
  verify_operations n arr ops :=
sorry

theorem solve_array_single_element
  (n : Nat) (h : 0 < n) (h2 : n ≤ 100) :
  let arr := [1]
  let ops := solve_array_operations 1 arr
  List.length ops = 3 ∧
  ops[0]! = (1, 1, [0]) ∧
  ops[1]! = (1, 1, [0]) ∧
  ops[2]! = (1, 1, [-1]) :=
sorry
-- </vc-theorems>