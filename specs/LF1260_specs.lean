-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nextPermutation (arr : List Int) : List Int :=
sorry

def solve (n k : Nat) (perms : List (List Int)) : List (List Int) :=
sorry

def isPermutation (arr1 arr2 : List Int) : Bool :=
sorry

def isSortedDesc (arr : List Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem next_permutation_preserves_elements (arr : List Int) :
  isPermutation arr (nextPermutation arr) = true :=
sorry

theorem next_permutation_idempotent_at_max {arr : List Int}
  (h : isSortedDesc arr) :
  nextPermutation arr = arr :=
sorry

theorem next_permutation_lexicographically_larger {arr : List Int} :
  nextPermutation arr ≥ arr ∨ isSortedDesc arr :=
sorry

theorem solve_returns_correct_length (n k : Nat) (perms : List (List Int)) :
  (solve n k perms).length = perms.length :=
sorry

theorem solve_preserves_permutations (n k : Nat) (perms : List (List Int)) :
  ∀ i, i < perms.length →
    isPermutation (perms.get ⟨i, sorry⟩) ((solve n k perms).get ⟨i, sorry⟩) = true :=
sorry
-- </vc-theorems>