-- <vc-helpers>
-- </vc-helpers>

def logical_calc (lst : List Bool) (op : String) : Bool := sorry

def isOdd (n : Nat) : Bool :=
  n % 2 = 1

theorem logical_calc_and {lst : List Bool} (h : lst.length > 0) :
  logical_calc lst "AND" = lst.all id := sorry

theorem logical_calc_or {lst : List Bool} (h : lst.length > 0) :
  logical_calc lst "OR" = lst.any id := sorry

theorem logical_calc_xor {lst : List Bool} (h : lst.length > 0) :
  logical_calc lst "XOR" = isOdd (lst.filter id).length := sorry

theorem logical_calc_invalid_op {lst : List Bool} (op : String) (h : op ≠ "AND" ∧ op ≠ "OR" ∧ op ≠ "XOR") :
  logical_calc lst op = false := sorry

theorem logical_calc_associative {lst : List Bool} (op : String)
    (h1 : lst.length > 1)
    (h2 : op = "AND" ∨ op = "OR" ∨ op = "XOR") :
  let mid := lst.length / 2
  let left := logical_calc (lst.take mid) op
  let right := logical_calc (lst.drop mid) op
  logical_calc [left, right] op = logical_calc lst op := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval logical_calc [True, True, False] "AND"

/-
info: True
-/
-- #guard_msgs in
-- #eval logical_calc [True, True, False] "OR"

/-
info: False
-/
-- #guard_msgs in
-- #eval logical_calc [True, True, False] "XOR"

-- Apps difficulty: introductory
-- Assurance level: unguarded