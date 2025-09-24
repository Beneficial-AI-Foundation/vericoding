-- <vc-preamble>
def REGION : String := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

def charAtPos (s : String) (pos : Nat) : Char := s.data[pos]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encrypt (s : String) : String :=
sorry

def decrypt (s : String) : String :=
sorry

def isValidText (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encryption_decryption_roundtrip (s : String) (h : isValidText s = true) :
  decrypt (encrypt s) = s :=
sorry

theorem encrypted_uses_valid_chars (s : String) (h : isValidText s = true) (h2 : s ≠ "") :
  isValidText (encrypt s) = true :=
sorry

theorem invalid_chars_raise_exception (s : String) (h : isValidText s = false) :
  encrypt s = "" ∧ decrypt s = "" :=
sorry

theorem empty_string :
  encrypt "" = "" ∧ decrypt "" = "" :=
sorry

theorem second_chars_different (s : String) (h : isValidText s = true) (h2 : s.length ≥ 2) :
  encrypt s ≠ s :=
sorry

theorem first_char_mirrored (s : String) (h : isValidText s = true) (h2 : s ≠ "") :
  (charAtPos (encrypt s) 0) = (charAtPos REGION (REGION.length - 1)) :=
sorry
-- </vc-theorems>