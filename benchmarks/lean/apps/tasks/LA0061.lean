-- <vc-preamble>
def count_occurrences (s : List Nat) (value : Nat) : Nat :=
  match s with
  | [] => 0
  | h :: t => if h = value then 1 + count_occurrences t value else count_occurrences t value

def sum_seq (s : List Nat) : Nat :=
  match s with
  | [] => 0
  | h :: t => h + sum_seq t

def subarray_matches_desired (subarray : List Nat) (desired : List Nat) (m : Nat) : Prop :=
  desired.length = m ∧
  ∀ color, 1 ≤ color ∧ color ≤ m → count_occurrences subarray color = desired.get! (color - 1)

def ValidInput (n m : Nat) (colors desired : List Nat) : Prop :=
  colors.length = n ∧
  desired.length = m ∧
  (∀ i, 0 ≤ i ∧ i < colors.length → 1 ≤ colors.get! i ∧ colors.get! i ≤ m) ∧
  (∀ i, 0 ≤ i ∧ i < desired.length → 0 ≤ desired.get! i) ∧
  sum_seq desired ≤ n

@[reducible, simp]
def solve_precond (n m : Nat) (colors desired : List Nat) : Prop :=
  ValidInput n m colors desired
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Nat) (colors desired : List Nat) (h_precond : solve_precond n m colors desired) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Nat) (colors desired : List Nat) (result : String) (h_precond : solve_precond n m colors desired) : Prop :=
  (result = "YES" ↔ ∃ i j, 0 ≤ i ∧ i ≤ j ∧ j < n ∧ subarray_matches_desired (colors.drop i |>.take (j + 1 - i)) desired m) ∧
  (result = "YES" ∨ result = "NO")

theorem solve_spec_satisfied (n m : Nat) (colors desired : List Nat) (h_precond : solve_precond n m colors desired) :
    solve_postcond n m colors desired (solve n m colors desired h_precond) h_precond := by
  sorry
-- </vc-theorems>