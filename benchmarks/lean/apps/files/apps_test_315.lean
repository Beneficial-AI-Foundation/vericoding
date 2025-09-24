-- <vc-preamble>
def sum (s : List Int) : Int :=
  match s with
  | [] => 0
  | x :: xs => x + sum xs

def ValidInput (n : Int) (k : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ a.length = Int.natAbs n ∧ k ≥ 0 ∧ ∀ i, 0 ≤ i ∧ i < n → a[Int.natAbs i]! ≥ 0

def ValidOutput (a : List Int) (finalSchedule : List Int) (additionalWalks : Int) (k : Int) : Prop :=
  finalSchedule.length = a.length ∧
  additionalWalks ≥ 0 ∧
  (∀ i, 0 ≤ i ∧ i < Int.ofNat a.length → finalSchedule[Int.natAbs i]! ≥ a[Int.natAbs i]!) ∧
  (∀ i, 0 ≤ i ∧ i < Int.ofNat a.length - 1 → finalSchedule[Int.natAbs i]! + finalSchedule[Int.natAbs (i + 1)]! ≥ k) ∧
  additionalWalks = sum finalSchedule - sum a

@[reducible, simp]
def solve_precond (n : Int) (k : Int) (a : List Int) : Prop :=
  ValidInput n k a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (k : Int) (a : List Int) (h_precond : solve_precond n k a) : Int × List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (k : Int) (a : List Int) (result : Int × List Int) (h_precond : solve_precond n k a) : Prop :=
  ValidOutput a result.2 result.1 k

theorem solve_spec_satisfied (n : Int) (k : Int) (a : List Int) (h_precond : solve_precond n k a) :
    solve_postcond n k a (solve n k a h_precond) h_precond := by
  sorry
-- </vc-theorems>