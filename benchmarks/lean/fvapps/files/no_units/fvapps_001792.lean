-- <vc-preamble>
def beautiful_array (n : Nat) : List Nat :=
  sorry

def is_permutation (arr : List Nat) (n : Nat) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_beautiful_property (arr : List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem beautiful_array_correct (n : Nat) : 
  let arr := beautiful_array n
  n > 0 → (
    -- Length is correct
    arr.length = n ∧ 
    -- Is permutation of 1..n
    is_permutation arr n = true ∧
    -- Beautiful property holds
    check_beautiful_property arr = true
  ) :=
  sorry

theorem beautiful_array_small_cases :
  ∀ n : Nat, n ≤ 5 → n > 0 →
    let arr := beautiful_array n
    arr.length = n ∧
    is_permutation arr n = true ∧ 
    check_beautiful_property arr = true :=
  sorry
-- </vc-theorems>