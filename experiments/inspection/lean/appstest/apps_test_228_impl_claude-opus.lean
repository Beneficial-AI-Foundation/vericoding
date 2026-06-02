import Mathlib
-- <vc-preamble>
def minimum (s : List Int) : Int :=
  match s with
  | [] => 0  -- dummy value, should not be called on empty list
  | [x] => x
  | x :: xs => 
    let min_rest := minimum xs
    if x ≤ min_rest then x else min_rest

def countOccurrences (s : List Int) (val : Int) : Int :=
  match s with
  | [] => 0
  | x :: xs => (if x = val then 1 else 0) + countOccurrences xs val

def ValidInput (n : Int) (piles : List Int) : Prop :=
  n ≥ 2 ∧ n % 2 = 0 ∧ piles.length = n ∧ ∀ i, 0 ≤ i ∧ i < piles.length → piles[i]! ≥ 1

@[reducible, simp]
def solve_precond (n : Int) (piles : List Int) : Prop :=
  ValidInput n piles
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (piles : List Int) (h_precond : solve_precond n piles) : String :=
  let minVal := minimum piles
  let count := countOccurrences piles minVal
  if count > n / 2 then "Bob" else "Alice"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (piles : List Int) (result : String) (h_precond : solve_precond n piles) : Prop :=
  (result = "Alice" ∨ result = "Bob") ∧
  (piles.length > 0 → 
    (let minVal := minimum piles
     let count := countOccurrences piles minVal
     result = (if count > n / 2 then "Bob" else "Alice"))) ∧
  (piles.length = 0 → result = "Alice")

theorem solve_spec_satisfied (n : Int) (piles : List Int) (h_precond : solve_precond n piles) :
    solve_postcond n piles (solve n piles h_precond) h_precond := by
  unfold solve_postcond solve
  simp [solve_precond, ValidInput] at h_precond
  constructor
  · -- Prove result is either "Alice" or "Bob"
    by_cases h : countOccurrences piles (minimum piles) > n / 2
    · simp [h]
    · simp [h]
  constructor
  · -- Main case: piles.length > 0
    intro h_pos
    simp
  · -- Edge case: piles.length = 0 (shouldn't happen given precondition)
    intro h_zero
    -- This case contradicts the precondition
    have : piles.length = n := h_precond.2.2.1
    have : n ≥ 2 := h_precond.1
    omega
-- </vc-theorems>
