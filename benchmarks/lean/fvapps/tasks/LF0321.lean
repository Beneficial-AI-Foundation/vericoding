-- <vc-preamble>
def isWhitespace (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\r'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_numeric (s : String) : Bool :=
sorry

def isInteger (s : String) : Bool :=
sorry

def isDecimal (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem integer_pattern (s : String)
  (h : isInteger s) :
  is_numeric s = true :=
sorry

theorem decimal_pattern (s : String)
  (h : isDecimal s) :
  is_numeric s = true :=
sorry

theorem invalid_chars (s : String)
  (h₁ : s.length > 0)
  (h₂ : ∀ c ∈ s.data, c ∈ ['a', 'b', 'c', 'd', 'f', 'g', 'h', 'i', 'j', 'k', 'l',
                           'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w',
                           'x', 'y', 'z', 'A', 'B', 'C', 'D', 'F', 'G', 'H', 'I',
                           'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T',
                           'U', 'V', 'W', 'X', 'Y', 'Z', '!', '@', '#', '$', '%',
                           '^', '&', '*', '(', ')', '_', '{', '}', '[', ']', ';',
                           ':', '<', '>', '?'])
  (h₃ : ∀ c ∈ s.data, c ≠ 'e' ∧ c ≠ 'E') :
  is_numeric s = false :=
sorry

theorem whitespace_handling (s : String) (ws : String)
  (h₁ : ∀ c ∈ ws.data, isWhitespace c)
  (h₂ : isInteger s ∨ isDecimal s)
  (h₃ : s.trim ≠ "") :
  is_numeric (ws ++ s ++ ws) = is_numeric s :=
sorry
-- </vc-theorems>