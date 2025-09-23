-- <vc-preamble>
def ValidPermutation (p : List Int) (n : Int) : Prop :=
  p.length = n.natAbs ∧ n ≥ 1 ∧
  (∀ i, 0 ≤ i ∧ i < n → 1 ≤ p[i.natAbs]! ∧ p[i.natAbs]! ≤ n) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < n → p[i.natAbs]! ≠ p[j.natAbs]!)

def countRecordsFromIndex (s : List Int) (index : Nat) (maxSoFar : Int) : Int :=
  if index ≥ s.length then 0
  else if s[index]! > maxSoFar then 
    1 + countRecordsFromIndex s (index + 1) s[index]!
  else countRecordsFromIndex s (index + 1) maxSoFar
termination_by s.length - index

def countRecords (s : List Int) : Int :=
  if s.length = 0 then 0
  else 1 + countRecordsFromIndex s 1 s[0]!

def indexOf (p : List Int) (elem : Int) : Nat :=
  match p.findIdx? (· = elem) with
  | some idx => idx
  | none => 0

def countRecordsAfterRemoval (p : List Int) (toRemove : Int) : Int :=
  let removeIdx := indexOf p toRemove
  let filtered := (List.range (p.length - 1)).map (fun i =>
    if removeIdx ≤ i then p[i + 1]! else p[i]!)
  countRecords filtered

@[reducible, simp]
def solve_precond (n : Int) (p : List Int) : Prop :=
  ValidPermutation p n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (p : List Int) (h_precond : solve_precond n p) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (p : List Int) (result : Int) (h_precond : solve_precond n p) : Prop :=
  1 ≤ result ∧ result ≤ n ∧
  result ∈ p ∧
  (∀ x, x ∈ p → countRecordsAfterRemoval p result ≥ countRecordsAfterRemoval p x) ∧
  (∀ x, x ∈ p ∧ countRecordsAfterRemoval p x = countRecordsAfterRemoval p result → result ≤ x)

theorem solve_spec_satisfied (n : Int) (p : List Int) (h_precond : solve_precond n p) :
    solve_postcond n p (solve n p h_precond) h_precond := by
  sorry
-- </vc-theorems>