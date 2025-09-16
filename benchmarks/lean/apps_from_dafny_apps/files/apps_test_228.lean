-- <vc-preamble>
-- <vc-preamble>
def minimum (s : List Int) : Int :=
  sorry

def countOccurrences (s : List Int) (val : Int) : Int :=
  sorry

def ValidInput (n : Int) (piles : List Int) : Prop :=
  n ≥ 2 ∧ n % 2 = 0 ∧ piles.length = n ∧ ∀ i, 0 ≤ i ∧ i < piles.length → piles[i]! ≥ 1

@[reducible, simp]
def solve_precond (n : Int) (piles : List Int) : Prop :=
  ValidInput n piles
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (n : Int) (piles : List Int) (h_precond : solve_precond n piles) : String :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>
