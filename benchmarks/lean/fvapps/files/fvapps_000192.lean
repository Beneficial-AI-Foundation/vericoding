-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxSubarraySumCircular (nums : List Int) : Int :=
sorry

def isEmpty (nums : List Int) : Bool :=
sorry

def maxElem (nums : List Int) : Int :=
sorry

def sumList (nums : List Int) : Int :=
sorry

def isAllPositive (nums : List Int) : Bool :=
sorry

def isAllNegative (nums : List Int) : Bool :=
sorry

def rotate (nums : List Int) (i : Nat) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element (nums : List Int) (h : nums.length = 1) (first : Int) :
  nums = [first] → maxSubarraySumCircular nums = first :=
sorry
-- </vc-theorems>