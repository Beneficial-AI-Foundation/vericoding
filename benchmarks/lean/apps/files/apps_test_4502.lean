-- <vc-preamble>

def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ a.length = n

def reverseSeq (s : List Int) : List Int :=
  s.reverse

partial def simulateOperations (a : List Int) : List Int :=
  if a.length = 1 then 
    [a[0]!]
  else
    let prev := simulateOperations (a.take (a.length - 1))
    reverseSeq (prev ++ [a[a.length - 1]!])

def computeResult (a : List Int) : List Int :=
  let n := a.length
  let o := (List.range (if n % 2 = 0 then n / 2 else (n + 1) / 2)).map (fun i => a[2*i]!)
  let e := (List.range (n / 2)).map (fun i => a[2*i + 1]!)
  if n % 2 = 0 then
    reverseSeq e ++ o
  else
    reverseSeq o ++ e

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (h_precond : solve_precond n a) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (result : List Int) (h_precond : solve_precond n a) : Prop :=
  result.length = n ∧ result = computeResult a

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>