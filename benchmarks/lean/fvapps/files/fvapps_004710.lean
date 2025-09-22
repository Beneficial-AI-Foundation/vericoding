-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def word_problem (rules : List (String × String)) (from_str to_str : String) (applications : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem word_problem_returns_bool (rules : List (String × String)) (from_str to_str : String) (applications : Nat) :
  word_problem rules from_str to_str applications = true ∨ word_problem rules from_str to_str applications = false :=
  sorry

theorem word_problem_zero_applications (rules : List (String × String)) (from_str to_str : String) :
  word_problem rules from_str to_str 0 = (from_str = to_str) :=
  sorry

theorem word_problem_equal_strings (rules : List (String × String)) (str : String) (n : Nat) :
  n > 0 → word_problem rules str str n = true :=
  sorry

theorem word_problem_impossible_match (rules : List (String × String)) (from_str impossible : String) (n : Nat) :
  n > 0 →
  String.length impossible > String.length from_str + n →
  word_problem rules from_str impossible n = false :=
  sorry

theorem word_problem_single_rule (from_str to_str : String) :
  word_problem [(from_str, to_str)] from_str to_str 1 = true :=
  sorry
-- </vc-theorems>