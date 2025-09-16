-- <vc-preamble>
-- <vc-preamble>
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧
  a.length = Int.natAbs n ∧
  (∀ i, 0 ≤ i ∧ i < Int.natAbs n → 1 ≤ a[i]! ∧ a[i]! ≤ n) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < Int.natAbs n → a[i]! ≠ a[j]!)

def ValidOutput (n : Int) (result : Int) : Prop :=
  0 ≤ result ∧ result ≤ n

def ReversedArray (a : List Int) : List Int :=
  if a.length ≥ 1 then
    List.range a.length |>.map (fun i => a[a.length - 1 - i]!)
  else
    []

def HasIncreasingPair (ar : List Int) : Prop :=
  ∃ i, 1 ≤ i ∧ i < ar.length ∧ ar[i]! > ar[i-1]!

def MinIndex (ar : List Int) (n : Int) : Int :=
  sorry

def CorrectResult (n : Int) (a : List Int) : Int :=
  sorry

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (n : Int) (a : List Int) (h_precond : solve_precond n a) : Int :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (result : Int) (h_precond : solve_precond n a) : Prop :=
  ValidOutput n result ∧ result = CorrectResult n a

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
