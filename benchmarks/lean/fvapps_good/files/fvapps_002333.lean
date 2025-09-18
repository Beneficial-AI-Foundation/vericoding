-- <vc-preamble>
def String.freq (s : String) (c : Char) : Nat :=
  s.toList.filter (· = c) |>.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_palindrome (s : String) : Nat := sorry

theorem longest_palindrome_length_bounds 
  (s : String) (h : s.length > 0) : 
  let res := longest_palindrome s
  res ≤ s.length ∧ res ≥ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longest_palindrome_monotonic
  (s : String) (h : s.length > 0) :
  let res1 := longest_palindrome s
  let res2 := longest_palindrome (s.push 'a')
  res2 ≥ res1 := sorry

theorem longest_palindrome_repeated_char
  (s : String) (h : s.length > 0) :
  let c := s.get 0
  let repeated := String.mk (List.replicate s.length c)
  longest_palindrome repeated = s.length := sorry

theorem longest_palindrome_single_space :
  longest_palindrome " " = 1 := sorry
-- </vc-theorems>