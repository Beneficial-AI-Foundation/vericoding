-- <vc-preamble>
def maxSubarraySumCircular (nums : List Int) : Int := sorry

def isEmpty (nums : List Int) : Bool := sorry

def maxElem (nums : List Int) : Int := sorry 

def sumList (nums : List Int) : Int := sorry

def isAllPositive (nums : List Int) : Bool := sorry

def isAllNegative (nums : List Int) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rotate (nums : List Int) (i : Nat) : List Int := sorry

theorem single_element (nums : List Int) (h : nums.length = 1) (first : Int) :
  nums = [first] → maxSubarraySumCircular nums = first := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 3
-/
-- #guard_msgs in
-- #eval maxSubarraySumCircular [-2, 3, -2, 1]

/-
info: 10
-/
-- #guard_msgs in
-- #eval maxSubarraySumCircular [5, -3, 5]

/-
info: -1
-/
-- #guard_msgs in
-- #eval maxSubarraySumCircular [-2, -3, -1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible