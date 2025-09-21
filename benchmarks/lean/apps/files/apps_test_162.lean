-- <vc-preamble>
def ValidInput (n k : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ a.length = n.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < a.length → a[i]! ≥ 1) ∧
  (∃ i, 0 ≤ i ∧ i < a.length ∧ k % a[i]! = 0)

def ValidBucket (k bucketSize : Int) : Prop :=
  bucketSize ≥ 1 ∧ k % bucketSize = 0

def HoursNeeded (k bucketSize : Int) : Int :=
  k / bucketSize

def IsOptimalChoice (k : Int) (a : List Int) (chosenBucket : Int) : Prop :=
  0 ≤ chosenBucket ∧ chosenBucket.natAbs < a.length ∧
  ValidBucket k a[chosenBucket.natAbs]! ∧
  (∀ i, 0 ≤ i ∧ i < a.length ∧ ValidBucket k a[i]! → a[i]! ≤ a[chosenBucket.natAbs]!)

@[reducible, simp]
def solve_precond (n k : Int) (a : List Int) : Prop :=
  ValidInput n k a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (a : List Int) (h_precond : solve_precond n k a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (a : List Int) (result : Int) (h_precond : solve_precond n k a) : Prop :=
  result ≥ 1 ∧
  ∃ i, IsOptimalChoice k a i ∧ result = HoursNeeded k a[i.natAbs]!

theorem solve_spec_satisfied (n k : Int) (a : List Int) (h_precond : solve_precond n k a) :
    solve_postcond n k a (solve n k a h_precond) h_precond := by
  sorry
-- </vc-theorems>