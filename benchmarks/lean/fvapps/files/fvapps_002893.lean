-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : Bool := sorry

def reverse (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_returns_bool (s : String) : 
  solve s = true ∨ solve s = false := sorry

theorem empty_or_single_char_is_palindrome (s : String) :
  s.length ≤ 1 → solve s = true := sorry

theorem palindrome_concat_is_palindrome (s : String) :
  let palindrome := s ++ reverse s
  solve palindrome = true := sorry

theorem same_chars_is_palindrome (s : String) (n : Nat) :
  let same_chars := String.mk (List.replicate n 'a')
  solve same_chars = true := sorry

theorem palindrome_stays_after_rotation (s : String) :
  s.length ≥ 2 →
  solve s = true →
  let rotated := (s.drop 1) ++ (s.take 1)
  solve rotated = true := sorry
-- </vc-theorems>