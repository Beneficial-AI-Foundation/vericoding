-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pattern (n : Nat) : List (List Nat) :=
  sorry

def sumRange (a b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem triangle_numbers (n : Nat) (h : n > 0) :
  let pattern := generate_pattern n
  ∀ i, i < n → (pattern.get! i).get! 0 = sumRange 1 (i+2) :=
sorry

theorem pattern_differences (n : Nat) (h : n > 0) :
  let pattern := generate_pattern n
  ∀ i j, i < n → j + 1 < (pattern.get! i).length →
    let row := pattern.get! i
    let diff := row.get! (j+1) - row.get! j
    if j + i + 1 < n
      then diff = j + i + 1
      else diff = 2*n - (j + i + 1) - 1 :=
sorry
-- </vc-theorems>