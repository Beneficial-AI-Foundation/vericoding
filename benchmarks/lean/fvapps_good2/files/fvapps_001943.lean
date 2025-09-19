-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_palindrome (s : String) : Bool :=
  sorry

def solve_palindrome_cuts (s : String) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_result_in_valid_range
  (s : String)
  (h : s.length > 0) :
  let result := solve_palindrome_cuts s
  result = none ∨ result = some 1 ∨ result = some 2 :=
sorry

theorem palindrome_gives_impossible
  (s : String)
  (h : is_palindrome s = true) :
  solve_palindrome_cuts s = none :=
sorry

theorem result_one_implies_palindrome_rotation
  (s : String)
  (h : solve_palindrome_cuts s = some 1) :
  ∃ i : Nat, i ≤ s.length ∧
    is_palindrome (s.drop i ++ s.take i) = true :=
sorry

theorem result_preserves_length
  (s : String)
  (h : s.length > 0) :
  (solve_palindrome_cuts s).isSome → s.length > 0 :=
sorry

theorem repeated_char_impossible
  (c : Char)
  (n : Nat)
  (h : n > 0) :
  solve_palindrome_cuts (String.mk (List.replicate n c)) = none :=
sorry

theorem short_strings_impossible
  (s : String)
  (h : s.length ≤ 2) :
  solve_palindrome_cuts s = none :=
sorry
-- </vc-theorems>