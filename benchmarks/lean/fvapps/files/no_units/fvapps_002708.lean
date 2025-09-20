-- <vc-preamble>
def abs (n : Int) : Int :=
  sorry

def sum (lst : List Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def modified_sum (lst : List Int) (p : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem modified_sum_p_one {lst : List Int} (h : lst ≠ []) : 
  modified_sum lst 1 = 0 := sorry
-- </vc-theorems>