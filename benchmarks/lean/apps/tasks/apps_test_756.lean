-- <vc-preamble>
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ n ≤ 90 ∧
  a.length = Int.natAbs n ∧
  (∀ i, 0 ≤ i ∧ i < n → ∃ h : Int.natAbs i < a.length, 1 ≤ a[Int.natAbs i] ∧ a[Int.natAbs i] ≤ 90) ∧
  (∀ i, 0 ≤ i ∧ i < n - 1 → ∃ h1 : Int.natAbs i < a.length, ∃ h2 : Int.natAbs (i + 1) < a.length, a[Int.natAbs i] < a[Int.natAbs (i + 1)])

def findCutoff (a : List Int) (index : Int) (cutoff : Int) : Int :=
  if h : index ≥ a.length then cutoff
  else if index ≥ 0 ∧ Int.natAbs index < a.length ∧ a[Int.natAbs index]! > cutoff then cutoff
  else if index ≥ 0 ∧ Int.natAbs index < a.length then findCutoff a (index + 1) (a[Int.natAbs index]! + 15)
  else cutoff
termination_by a.length - Int.natAbs index

def minInt (x y : Int) : Int :=
  if x ≤ y then x else y

def ValidOutput (result : Int) (n : Int) (a : List Int) : Prop :=
  ValidInput n a →
  (1 ≤ result ∧ result ≤ 90 ∧
   result = minInt 90 (findCutoff a 0 15))

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (h_precond : solve_precond n a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (result : Int) (h_precond : solve_precond n a) : Prop :=
  ValidOutput result n a

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>