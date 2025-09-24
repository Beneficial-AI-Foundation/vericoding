-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pattern (k : Nat) : List String := sorry

theorem valid_chars {k : Nat} :
  ∀ line ∈ generate_pattern k,
  ∀ c ∈ line.data,
  c.isDigit ∨ c = ' ' := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>