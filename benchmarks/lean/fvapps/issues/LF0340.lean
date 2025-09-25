-- <vc-preamble>
def delete_and_earn (nums : List Nat) : Nat := sorry

def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + List.sum xs

def List.maximum' : List Nat → Nat 
  | [] => 0
  | [x] => x
  | (x::xs) => max x (List.maximum' xs)

def isConsecutive (nums : List Nat) : Bool := sorry

def sumByParity (nums : List Nat) (isOdd : Bool) : Nat := 
  List.sum (List.filter (fun n => n % 2 = if isOdd then 1 else 0) nums)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSpaced (nums : List Nat) : Bool := sorry

theorem spaced_numbers (nums : List Nat) (h : nums.length ≥ 2) :
  isSpaced nums = true →
  delete_and_earn nums = List.sum nums := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem delete_and_earn_properties (nums : List Nat) :
  let result := delete_and_earn nums;
  (nums = [] → result = 0) ∧
  (nums ≠ [] →
    let max_num := List.maximum' nums;
    let max_count := (List.filter (fun x => x = max_num) nums).length;
    result ≥ max_num * max_count) ∧
  result ≤ List.sum nums := sorry

theorem consecutive_numbers (nums : List Nat) (h : nums ≠ []) :
  isConsecutive nums = true →
  delete_and_earn nums = max (sumByParity nums true) (sumByParity nums false) := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval delete_and_earn [3, 4, 2]

/-
info: 9
-/
-- #guard_msgs in
-- #eval delete_and_earn [2, 2, 3, 3, 3, 4]

/-
info: 6
-/
-- #guard_msgs in
-- #eval delete_and_earn [2, 3, 4]
-- </vc-theorems>