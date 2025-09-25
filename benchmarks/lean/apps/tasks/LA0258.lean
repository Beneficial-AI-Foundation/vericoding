-- <vc-preamble>
def sum_window (heights : List Int) (start : Nat) (k : Nat) : Int :=
  match k with
  | 0 => 0
  | 1 => heights[start]!
  | k + 1 => heights[start]! + sum_window heights (start + 1) k
termination_by k

def ValidInput (n : Int) (k : Int) (heights : List Int) : Prop :=
  1 ≤ k ∧ k ≤ n ∧ heights.length = n.toNat ∧ ∀ i, 0 ≤ i ∧ i < n → 1 ≤ heights[i.toNat]! ∧ heights[i.toNat]! ≤ 100

def ValidResult (result : Int) (n : Int) (k : Int) (heights : List Int) : Prop :=
  1 ≤ result ∧ result ≤ n - k + 1 ∧
  (∀ start, 0 ≤ start ∧ start ≤ n - k → 
    sum_window heights (result - 1).toNat k.toNat ≤ sum_window heights start.toNat k.toNat) ∧
  (∀ start, 0 ≤ start ∧ start < result - 1 →
    sum_window heights start.toNat k.toNat > sum_window heights (result - 1).toNat k.toNat)

@[reducible, simp]
def solve_precond (n : Int) (k : Int) (heights : List Int) : Prop :=
  ValidInput n k heights
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (k : Int) (heights : List Int) (h_precond : solve_precond n k heights) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (k : Int) (heights : List Int) (result : Int) (h_precond : solve_precond n k heights) : Prop :=
  ValidResult result n k heights

theorem solve_spec_satisfied (n : Int) (k : Int) (heights : List Int) (h_precond : solve_precond n k heights) :
    solve_postcond n k heights (solve n k heights h_precond) h_precond := by
  sorry
-- </vc-theorems>