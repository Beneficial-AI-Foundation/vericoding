-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_negative_zero (x : Float) : Bool :=
sorry

def getSign (x : Float) : Float :=
sorry

def posInf : Float :=
sorry

def negInf : Float :=
sorry

def nanFloat : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_negative_zero_main (x : Float) :
  is_negative_zero x = true ↔ (getSign x < 0 ∧ x = 0) :=
sorry

theorem is_negative_zero_special_cases :
  is_negative_zero posInf = false ∧
  is_negative_zero negInf = false ∧
  is_negative_zero nanFloat = false :=
sorry

theorem is_negative_zero_integers (n : Int) :
  is_negative_zero (Float.ofInt n) = false :=
sorry
-- </vc-theorems>