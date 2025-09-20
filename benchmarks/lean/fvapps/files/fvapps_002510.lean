-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def evaluate_expression (expr : String) (locals : Option (String → Nat) := none) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arithmetic_addition (a b : Int) :
  evaluate_expression s!"{a} + {b}" = a + b :=
sorry

theorem arithmetic_multiplication (a b : Int) :
  evaluate_expression s!"{a} * {b}" = a * b :=
sorry

theorem local_variable_access (x : Nat) (locals : String → Nat) :
  locals "x" = x →
  evaluate_expression "x" (some locals) = x :=
sorry

theorem local_variable_multiplication (x : Nat) (locals : String → Nat) :
  locals "x" = x →
  evaluate_expression "x * 2" (some locals) = x * 2 :=
sorry

theorem builtin_string_length (s : String) (locals : String → Nat) :
  locals "s" = s.length →
  evaluate_expression "len(s)" (some locals) = s.length :=
sorry

theorem invalid_expression_raises_error :
  evaluate_expression "2 +" = 0 :=
sorry

theorem undefined_variable_raises_error :
  evaluate_expression "undefined_var" = 0 :=
sorry
-- </vc-theorems>