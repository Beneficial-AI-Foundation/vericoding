import Mathlib
-- <vc-preamble>

@[reducible, simp]
def ValidInput (nums : List Int) : Prop :=
  nums.length = 3 ∧
  (∀ i, 0 ≤ i ∧ i < nums.length → nums[i]! > 0) ∧
  (∀ i, 0 ≤ i ∧ i < nums.length → nums[i]! ≤ 1500)

def sortThree (x y z : Int) : Int × Int × Int :=
  if x ≤ y ∧ x ≤ z then
    if y ≤ z then (x, y, z) else (x, z, y)
  else if y ≤ x ∧ y ≤ z then
    if x ≤ z then (y, x, z) else (y, z, x)
  else
    if x ≤ y then (z, x, y) else (z, y, x)

def computeResult (x y z : Int) : String :=
  if x > 0 ∧ y > 0 ∧ z > 0 ∧ x ≤ 1500 ∧ y ≤ 1500 ∧ z ≤ 1500 then
    let sorted := sortThree x y z
    let a := sorted.1
    let b := sorted.2.1
    let c := sorted.2.2
    if a > 3 then "NO"
    else if a = 3 then
      if b > 3 then "NO"
      else if b = 3 then
        if c > 3 then "NO" else "YES"
      else "NO"
    else if a = 1 then "YES"
    else
      if b = 2 then "YES"
      else if b > 4 then "NO"
      else if b = 4 then
        if c = 4 then "YES" else "NO"
      else "NO"
  else "NO"

@[reducible, simp]
def solve_precond (nums : List Int) : Prop :=
  ValidInput nums
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem computeResult_cases (x y z : Int) : computeResult x y z = "YES" ∨ computeResult x y z = "NO" := by
  unfold computeResult
  grind

-- </vc-helpers>

-- <vc-definitions>
def solve (nums : List Int) (h_precond : solve_precond nums) : String :=
  computeResult nums[0]! nums[1]! nums[2]!
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (nums : List Int) (result : String) (h_precond : solve_precond nums) : Prop :=
  (result = "YES" ∨ result = "NO") ∧
  result = computeResult nums[0]! nums[1]! nums[2]!

theorem solve_spec_satisfied (nums : List Int) (h_precond : solve_precond nums) :
    solve_postcond nums (solve nums h_precond) h_precond := by
  have h_yesno : computeResult nums[0]! nums[1]! nums[2]! = "YES" ∨ computeResult nums[0]! nums[1]! nums[2]! = "NO" := computeResult_cases nums[0]! nums[1]! nums[2]!
  unfold solve_postcond
  constructor
  · exact h_yesno
  · rfl
-- </vc-theorems>
