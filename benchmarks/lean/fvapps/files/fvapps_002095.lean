-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_psychos (n : Nat) (arr : List Nat) : Nat :=
  sorry

def is_sorted_desc (arr : List Nat) : Bool :=
  sorry

def is_strictly_sorted_asc (arr : List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_single_array :
  solve_psychos 0 [] = 0 ∧
  ∀ x : Nat, solve_psychos 1 [x] = 0 :=
sorry

theorem solve_psychos_bounds :
  ∀ (n : Nat) (arr : List Nat),
  arr.length = n →
  0 ≤ solve_psychos n arr ∧
  solve_psychos n arr ≤ n - 1 :=
sorry
-- </vc-theorems>