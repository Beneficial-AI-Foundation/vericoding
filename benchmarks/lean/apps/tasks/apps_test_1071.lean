-- <vc-preamble>
def ValidInput (a b : List Int) (n : Int) : Prop :=
  a.length ≥ 0 ∧ b.length ≥ 0 ∧
  (∀ i, 0 ≤ i ∧ i < a.length → a[i]! ≥ 0) ∧
  (∀ j, 0 ≤ j ∧ j < b.length → b[j]! ≥ 0) ∧
  n ≥ 1

def sum_seq (s : List Int) : Int :=
  s.sum

def ShelvesNeeded (total capacity : Int) : Int :=
  if total = 0 then 0 else (total - 1) / capacity + 1

def CanPlaceAll (a b : List Int) (n : Int) : Bool :=
  let total_cups := sum_seq a
  let total_medals := sum_seq b
  let shelves_for_cups := ShelvesNeeded total_cups 5
  let shelves_for_medals := ShelvesNeeded total_medals 10
  shelves_for_cups + shelves_for_medals ≤ n

@[reducible, simp]
def solve_precond (a b : List Int) (n : Int) : Prop :=
  ValidInput a b n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : List Int) (n : Int) (h_precond : solve_precond a b n) : String :=
  if CanPlaceAll a b n then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : List Int) (n : Int) (result: String) (h_precond : solve_precond a b n) : Prop :=
  result = (if CanPlaceAll a b n then "YES" else "NO")

theorem solve_spec_satisfied (a b : List Int) (n : Int) (h_precond : solve_precond a b n) :
    solve_postcond a b n (solve a b n h_precond) h_precond := by
  simp [solve, solve_postcond]
-- </vc-theorems>