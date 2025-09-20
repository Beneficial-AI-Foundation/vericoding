-- <vc-preamble>
def getUnique (arr : List Int) : List Int :=
  arr.foldl (fun acc x => if acc.contains x then acc else x::acc) []

def sumList (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => x + sumList xs

def filterPositive (l : List Int) : List Int :=
  l.filter (fun x => x > 0)

def filterNegative (l : List Int) : List Int :=
  l.filter (fun x => x < 0)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (arr : List Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_invariant_under_duplication : ∀ (arr : List Int),
  arr ≠ [] → solve (arr ++ arr) = solve arr :=
sorry

theorem solve_positive_result_implies_positive_element : ∀ (arr : List Int),
  arr ≠ [] → solve arr > 0 → ∃ x ∈ arr, x > 0 :=
sorry

theorem solve_negative_result_implies_negative_element : ∀ (arr : List Int),
  arr ≠ [] → solve arr < 0 → ∃ x ∈ arr, x < 0 :=
sorry
-- </vc-theorems>