-- <vc-preamble>
def is_valid_beautiful_arrangement (arrangement: List Int) (sizes: List Int) : Prop :=
  (∀ i : Nat, i < arrangement.length → 1 ≤ arrangement[i]! ∧ arrangement[i]! ≤ sizes.length) →
  (arrangement.length ≥ 1 ∧
   (∀ i j : Nat, i < j ∧ j < arrangement.length → arrangement[i]! ≠ arrangement[j]!) ∧
   (∀ i : Nat, i < arrangement.length - 1 → arrangement[i]! < arrangement[i + 1]!) ∧
   (∀ i : Nat, i < arrangement.length - 1 → arrangement[i + 1]! % arrangement[i]! = 0) ∧
   (∀ i : Nat, i < arrangement.length - 1 → sizes[Int.natAbs (arrangement[i]! - 1)]! < sizes[Int.natAbs (arrangement[i + 1]! - 1)]!))

def ValidInput (n: Int) (sizes: List Int) : Prop :=
  n ≥ 1 ∧ sizes.length = Int.natAbs n ∧ ∀ i : Nat, i < Int.natAbs n → sizes[i]! ≥ 1

@[reducible, simp]
def solve_precond (n : Int) (sizes : List Int) : Prop :=
  ValidInput n sizes
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (sizes : List Int) (h_precond : solve_precond n sizes) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (sizes : List Int) (result: Int) (h_precond : solve_precond n sizes) : Prop :=
  1 ≤ result ∧ result ≤ n ∧
  (∀ arrangement : List Int, (∀ i : Nat, i < arrangement.length → 1 ≤ arrangement[i]! ∧ arrangement[i]! ≤ sizes.length) ∧ is_valid_beautiful_arrangement arrangement sizes → arrangement.length ≤ Int.natAbs result) ∧
  (∃ arrangement : List Int, (∀ i : Nat, i < arrangement.length → 1 ≤ arrangement[i]! ∧ arrangement[i]! ≤ sizes.length) ∧ is_valid_beautiful_arrangement arrangement sizes ∧ arrangement.length = Int.natAbs result)

theorem solve_spec_satisfied (n : Int) (sizes : List Int) (h_precond : solve_precond n sizes) :
    solve_postcond n sizes (solve n sizes h_precond) h_precond := by
  sorry
-- </vc-theorems>