-- <vc-preamble>
def ValidInput (n : Int) (a : List Int) (p : String) : Prop :=
  n ≥ 2 ∧
  a.length = n ∧
  p.length = n - 1 ∧
  (∀ i, 0 ≤ i ∧ i < p.length → p.data[i]! = '0' ∨ p.data[i]! = '1') ∧
  (∀ i, 0 ≤ i ∧ i < a.length → 1 ≤ a[i]! ∧ a[i]! ≤ n) ∧
  (∀ i, 1 ≤ i ∧ i ≤ n → ∃ j, 0 ≤ j ∧ j < a.length ∧ a[j]! = i)

def max_up_to (a : List Int) (i : Nat) : Int :=
  if i = 0 then a[0]!
  else if a[i]! > max_up_to a (i-1) then a[i]!
  else max_up_to a (i-1)
termination_by i

def CanSort (n : Int) (a : List Int) (p : String) : Prop :=
  ValidInput n a p →
  ∀ i, 0 ≤ i ∧ i < n - 1 → 
    (p.data[Int.natAbs i]! = '0' → max_up_to a (Int.natAbs i) ≤ i + 1)

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) (p : String) : Prop :=
  ValidInput n a p
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (p : String) (h_precond : solve_precond n a p) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (p : String) (result : String) (h_precond : solve_precond n a p) : Prop :=
  (result = "YES" ∨ result = "NO") ∧
  (result = "YES" ↔ CanSort n a p)

theorem solve_spec_satisfied (n : Int) (a : List Int) (p : String) (h_precond : solve_precond n a p) :
    solve_postcond n a p (solve n a p h_precond) h_precond := by
  sorry
-- </vc-theorems>