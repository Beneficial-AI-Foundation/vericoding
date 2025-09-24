-- <vc-preamble>
def factorial (n : Nat) : Nat :=
  if n = 0 then 1 else n * factorial (n - 1)

def IsPermutation (perm : List Int) (original : List Int) : Prop :=
  perm.length = original.length ∧ ∀ x, perm.count x = original.count x

def AllDistinct (s : List Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < s.length → s[i]! ≠ s[j]!

def AllDistinctLists (result : List (List Int)) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < result.length → result[i]! ≠ result[j]!

@[reducible, simp]
def solve_precond (nums : List Int) : Prop :=
  AllDistinct nums
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (nums : List Int) (h_precond : solve_precond nums) : List (List Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (nums : List Int) (result : List (List Int)) (h_precond : solve_precond nums) : Prop :=
  result.length = factorial nums.length ∧
  (∀ p, p ∈ result → IsPermutation p nums) ∧
  AllDistinctLists result ∧
  (∀ perm, IsPermutation perm nums → perm ∈ result)

theorem solve_spec_satisfied (nums : List Int) (h_precond : solve_precond nums) :
    solve_postcond nums (solve nums h_precond) h_precond := by
  sorry
-- </vc-theorems>