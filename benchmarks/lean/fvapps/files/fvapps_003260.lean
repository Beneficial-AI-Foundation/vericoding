-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replace_zero (arr : List Nat) : Int := sorry

def consecutive_ones (l : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem replace_zero_valid_output (arr : List Nat)
    (h : ∀ x ∈ arr, x = 0 ∨ x = 1) : 
    -1 ≤ replace_zero arr ∧ replace_zero arr < arr.length := sorry

theorem replace_zero_no_zeros (arr : List Nat)
    (h1 : ∀ x ∈ arr, x = 0 ∨ x = 1)
    (h2 : ∀ x ∈ arr, x ≠ 0) :
    replace_zero arr = -1 := sorry

theorem replace_zero_optimal (arr : List Nat) (idx : Int)
    (h1 : ∀ x ∈ arr, x = 0 ∨ x = 1)
    (h2 : idx = replace_zero arr)
    (h3 : idx ≠ -1) :
    ∀ i, 0 ≤ i → i < arr.length →
        consecutive_ones (arr.set (Int.toNat idx) 1) ≥ consecutive_ones (arr.set (Int.toNat i) 1) := sorry

theorem replace_zero_padding (arr : List Nat)
    (h : ∀ x ∈ arr, x = 0 ∨ x = 1) :
    let padded := 0 :: arr ++ [0]
    replace_zero padded = -1 ∧ replace_zero arr = -1 ∨
    replace_zero padded = replace_zero arr + 1 ∨
    replace_zero padded = 0 ∨
    replace_zero padded = arr.length + 1 := sorry
-- </vc-theorems>