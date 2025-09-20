-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def strLen (s : String) : Nat :=
  sorry

def stringSuffix (s : String) : Nat :=
  sorry

def isRepeatedChar (s : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_suffix_positive (s : String) :
  stringSuffix s ≥ 0 :=
sorry

theorem string_suffix_ge_len (s : String) :
  stringSuffix s ≥ strLen s :=
sorry

theorem string_suffix_le_square (s : String) :
  stringSuffix s ≤ strLen s * strLen s :=
sorry

theorem string_suffix_repeated_char (s : String) :
  isRepeatedChar s → stringSuffix s = (strLen s * (strLen s + 1)) / 2 :=
sorry

theorem string_suffix_empty :
  stringSuffix "" = 0 :=
sorry

theorem string_suffix_slice (s : String) (i : Nat) :
  i < strLen s → stringSuffix (s.drop i) ≤ stringSuffix s :=
sorry
-- </vc-theorems>