-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def combine_strings : List String → String
  | _ => sorry

def countChar (s : String) (c : Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem combine_strings_length (strings : List String) :
  (combine_strings strings).length = List.foldl (· + ·) 0 (strings.map String.length) :=
sorry

theorem combine_strings_freq (strings : List String) (s : String) (c : Char)
  (h : s ∈ strings) :
  (countChar (combine_strings strings) c) ≥
  (countChar s c) :=
sorry

theorem combine_strings_empty :
  combine_strings [] = "" :=
sorry

theorem combine_strings_singleton (s : String) :
  combine_strings [s] = s :=
sorry
-- </vc-theorems>