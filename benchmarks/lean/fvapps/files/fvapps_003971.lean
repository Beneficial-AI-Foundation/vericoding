-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.sumAscii (s : String) : Nat :=
sorry

def highest_value (a b : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem highest_value_is_input (a b : String) :
  let result := highest_value a b
  result = a ∨ result = b :=
sorry

theorem highest_value_maximizes_sum (a b : String) :
  let result := highest_value a b
  String.sumAscii result ≥ String.sumAscii (if result = a then b else a) :=
sorry

theorem highest_value_equal_sums (a b : String) :
  String.sumAscii a = String.sumAscii b →
  highest_value a b = a :=
sorry

theorem highest_value_identical (s : String) :
  highest_value s s = s :=
sorry

theorem highest_value_nonempty (a b : String) :
  a.length > 0 →
  b.length > 0 →
  (highest_value a b).length > 0 :=
sorry
-- </vc-theorems>