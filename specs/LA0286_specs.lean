-- <vc-preamble>
def ValidInput (holds : List Int) : Prop :=
  holds.length ≥ 3 ∧ ∀ i, 0 ≤ i ∧ i < holds.length - 1 → holds[i]! < holds[i + 1]!

def maxDiffHelper (s : List Int) (index : Nat) (currentMax : Int) : Int :=
  if index ≥ s.length then currentMax
  else 
    let diff := s[index]! - s[index - 1]!
    let newMax := if diff > currentMax then diff else currentMax
    maxDiffHelper s (index + 1) newMax
termination_by s.length - index

def maxDiff (s : List Int) : Int :=
  if s.length ≤ 1 then 0
  else
    let maxSoFar := if s[1]! - s[0]! ≥ 0 then s[1]! - s[0]! else 0
    maxDiffHelper s 2 maxSoFar

@[reducible, simp]
def solve_precond (holds : List Int) : Prop :=
  ValidInput holds
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (holds : List Int) (h_precond : solve_precond holds) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (holds : List Int) (result : Int) (h_precond : solve_precond holds) : Prop :=
  result ≥ 0 ∧ 
  (∃ k, 1 ≤ k ∧ k < holds.length - 1 ∧ result = maxDiff ((holds.take k) ++ (holds.drop (k + 1)))) ∧
  (∀ k, 1 ≤ k ∧ k < holds.length - 1 → result ≤ maxDiff ((holds.take k) ++ (holds.drop (k + 1))))

theorem solve_spec_satisfied (holds : List Int) (h_precond : solve_precond holds) :
    solve_postcond holds (solve holds h_precond) h_precond := by
  sorry
-- </vc-theorems>