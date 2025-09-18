-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findMaxForm (strs : List String) (m n : Nat) : Nat := sorry

theorem findMaxForm_bounds {strs : List String} {m n : Nat} (h : strs.length > 0) :
  findMaxForm strs m n ≤ strs.length ∧ findMaxForm strs m n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem findMaxForm_empty_string {strs : List String} (h : strs.length > 0) :
  findMaxForm (strs ++ [""] ) 1 1 ≤ findMaxForm strs 1 1 + 1 := sorry
-- </vc-theorems>