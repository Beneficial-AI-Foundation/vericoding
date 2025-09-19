-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def break_palindrome (s : String) : String :=
sorry

def is_palindrome (s : String) : Bool :=
sorry

def strRepeat (c : Char) (n : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_char_palindrome (n : Nat) (h : n = 1) :
  break_palindrome (strRepeat 'a' n) = "" :=
sorry

theorem all_a_string_breaks_to_b (s : String) (h₁ : s.length ≥ 2) (h₂ : ∀ c ∈ s.data, c = 'a') :
  break_palindrome s = (s.dropRight 1).push 'b' :=
sorry

theorem break_gives_different_string (s : String) (h₁ : s.length ≥ 2) (h₂ : is_palindrome s = true) :
  break_palindrome s ≠ s :=
sorry

theorem break_gives_non_palindrome (s : String) (h₁ : s.length ≥ 2) (h₂ : is_palindrome s = true) :
  is_palindrome (break_palindrome s) = false :=
sorry

theorem break_preserves_length (s : String) (h₁ : s.length ≥ 2) (h₂ : is_palindrome s = true) :
  (break_palindrome s).length = s.length :=
sorry
-- </vc-theorems>