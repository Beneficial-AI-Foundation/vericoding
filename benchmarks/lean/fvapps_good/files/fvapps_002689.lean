-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def switch_it_up (n : Nat) : String := sorry

theorem switch_it_up_valid_format {n : Nat} (h : n < 10) :
  let result := switch_it_up n
  -- First character is uppercase
  result.length > 0 ∧
  Char.isUpper (result.front) ∧ 
  -- Rest are lowercase
  ∀ i : String.Pos, i.1 > 0 → Char.isLower (result.get i) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem switch_it_up_consistent {n : Nat} (h : n < 10) :
  switch_it_up n = switch_it_up n := sorry

theorem switch_it_up_injective {n1 n2 : Nat} (h1 : n1 < 10) (h2 : n2 < 10) :
  n1 ≠ n2 → switch_it_up n1 ≠ switch_it_up n2 := sorry
-- </vc-theorems>