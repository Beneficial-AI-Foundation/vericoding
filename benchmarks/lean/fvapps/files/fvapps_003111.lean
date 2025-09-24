-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_average [Add α] [Div α] [OfNat α 0] : List α → α :=
  sorry

def list_min : List Float → Float :=
  sorry

def list_max : List Float → Float :=
  sorry

def list_sum : List Float → Float :=
  sorry

def abs (x : Float) : Float :=
  sorry

def toFloat (n : Nat) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_average_empty {α} [Add α] [Div α] [OfNat α 0] (nums : List α) :
  nums = [] → find_average nums = 0 := by
sorry

theorem find_average_bounds (nums : List Float) (h : nums ≠ []) :
  list_min nums ≤ find_average nums ∧
  find_average nums ≤ list_max nums := by
sorry

theorem find_average_sum (nums : List Float) :
  abs (find_average nums * toFloat nums.length - list_sum nums) < 1e-10 := by
sorry

theorem find_average_float_empty (nums : List Float) :
  nums = [] → find_average nums = 0 := by
sorry

theorem find_average_float_type (nums : List Float) (h : nums ≠ []) :
  find_average nums + 0 = find_average nums := by
sorry

theorem find_average_float_sum (nums : List Float) :
  abs (find_average nums * toFloat nums.length - list_sum nums) < 1e-6 := by
sorry
-- </vc-theorems>