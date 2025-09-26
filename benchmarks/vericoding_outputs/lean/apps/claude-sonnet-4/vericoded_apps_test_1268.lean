import Mathlib
-- <vc-preamble>
def ValidInput (a b : List Int) : Prop :=
  a.length = b.length ∧ a.length ≥ 2 ∧ ∀ i, 0 ≤ i ∧ i < a.length → 0 ≤ a[i]! ∧ a[i]! ≤ b[i]!

def sumSeq (s : List Int) : Int :=
  match s with
  | [] => 0
  | x :: xs => x + sumSeq xs

def findMax (s : List Int) : Nat :=
  if h : s.length ≥ 1 then
    if s.length = 1 then 0
    else
      let restMax := findMax s.tail
      if s[0]! ≥ s.tail[restMax]! then 0 else restMax + 1
  else 0

def findMaxExcluding (s : List Int) (exclude : Nat) : Nat :=
  if h1 : s.length ≥ 2 ∧ exclude < s.length then
    if exclude = 0 then
      1 + findMax s.tail
    else if exclude = s.length - 1 then
      findMax (s.take (s.length - 1))
    else
      let leftPart := s.take exclude
      let rightPart := s.drop (exclude + 1)
      if leftPart.length > 0 ∧ rightPart.length > 0 then
        let leftMax := findMax leftPart
        let rightMax := exclude + 1 + findMax rightPart
        if s[leftMax]! ≥ s[rightMax]! then leftMax else rightMax
      else if leftPart.length > 0 then
        findMax leftPart
      else
        exclude + 1 + findMax rightPart
  else 0

def findTwoLargestSum (s : List Int) : Int :=
  if h : s.length ≥ 2 then
    let max1 := findMax s
    let max2 := findMaxExcluding s max1
    s[max1]! + s[max2]!
  else 0

@[reducible, simp]
def solve_precond (a b : List Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (a b : List Int) (h_precond : solve_precond a b) : String :=
  if findTwoLargestSum b ≥ sumSeq a then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : List Int) (result : String) (h_precond : solve_precond a b) : Prop :=
  (result = "YES" ∨ result = "NO") ∧ 
  (result = "YES" ↔ findTwoLargestSum b ≥ sumSeq a)

theorem solve_spec_satisfied (a b : List Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  unfold solve solve_postcond
  split_ifs with h <;> simp [h]
-- </vc-theorems>
