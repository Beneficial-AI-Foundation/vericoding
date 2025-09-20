-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isEven (x : Int) : Bool :=
  sorry

def isFloat (x : Float) : Bool :=
  sorry

def isEvenFloat (x : Float) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem even_plus_two (x : Int) :
  isEven x = isEven (x + 2) :=
sorry

theorem even_plus_one_diff (x : Int) :
  isEven x ≠ isEven (x + 1) :=
sorry

theorem times_two_even (x : Int) :
  isEven (x * 2) = true :=
sorry

theorem non_integer_float_not_even (x : Float) :
  ¬isFloat x → isEvenFloat x = false :=
sorry
-- </vc-theorems>