-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isBubbly (word : String) : Bool := sorry

def countBubblyWords (words : List String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_matches_definition (words : List String) :
  countBubblyWords words = (words.filter isBubbly).length := sorry

theorem count_is_non_negative (words : List String) :
  countBubblyWords words ≥ 0 := sorry

theorem count_cannot_exceed_length (words : List String) :
  countBubblyWords words ≤ words.length := sorry

theorem single_repeated_char (c : Char) (n : Nat) :
  let word := String.mk (List.replicate n c)
  if n % 2 = 0 
  then countBubblyWords [word] = 1
  else countBubblyWords [word] = 0 := sorry
-- </vc-theorems>