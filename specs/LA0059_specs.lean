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
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (piles : List Int) (h_precond : solve_precond n piles) : String :=
  sorry
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
  sorry
-- </vc-theorems>