def find_average [Add α] [Div α] [OfNat α 0] : List α → α 
  | [] => 0
  | xs => sorry

def list_min : List Float → Float 
  | [] => 0
  | (x::xs) => sorry

def list_max : List Float → Float
  | [] => 0
  | (x::xs) => sorry

def list_sum : List Float → Float
  | [] => 0
  | (x::xs) => sorry

-- <vc-helpers>
-- </vc-helpers>

def abs (x : Float) : Float := sorry

def toFloat (n : Nat) : Float := sorry

theorem find_average_empty {α} [Add α] [Div α] [OfNat α 0] (nums : List α) : 
  nums = [] → find_average nums = 0 := by sorry

theorem find_average_bounds (nums : List Float) (h : nums ≠ []) : 
  list_min nums ≤ find_average nums ∧ 
  find_average nums ≤ list_max nums := by sorry

theorem find_average_sum (nums : List Float) :
  abs (find_average nums * toFloat nums.length - list_sum nums) < 1e-10 := by sorry

theorem find_average_float_empty (nums : List Float) :
  nums = [] → find_average nums = 0 := by sorry

theorem find_average_float_type (nums : List Float) (h : nums ≠ []) : 
  find_average nums + 0 = find_average nums := by sorry

theorem find_average_float_sum (nums : List Float) :
  abs (find_average nums * toFloat nums.length - list_sum nums) < 1e-6 := by sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_average [1]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_average [1, 3, 5, 7]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_average []

-- Apps difficulty: introductory
-- Assurance level: unguarded