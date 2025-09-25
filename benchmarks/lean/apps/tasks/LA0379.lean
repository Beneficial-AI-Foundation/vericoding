-- <vc-preamble>
def SplitLinesSpec (_ : String) : List String := []

def SplitWhitespaceSpec (_ : String) : List String := []

def ParseIntSpec (_ : String) : Int := 0

def IntToStringResult (_ : Int) : String := "0"

def ValidInput (input : String) : Prop :=
  let lines := SplitLinesSpec input
  lines.length ≥ 1 ∧ 
  (SplitWhitespaceSpec (lines[0]!)).length ≥ 2 ∧
  let n := ParseIntSpec ((SplitWhitespaceSpec (lines[0]!))[0]!)
  let k := ParseIntSpec ((SplitWhitespaceSpec (lines[0]!))[1]!)
  n > 0 ∧ k > 0 ∧ lines.length ≥ Int.natAbs n + 1 ∧
  (∀ i, 1 ≤ i ∧ i ≤ Int.natAbs n → 
      i < lines.length ∧ (SplitWhitespaceSpec (lines[i]!)).length ≥ 2)

def SumRange (_ : List Int) (_ _ : Nat) : Int := 0

def MaxGapSquared (_ : List Int) (_ _ : Nat) : Int := 0

def IntMax (a b : Int) : Int := if a ≥ b then a else b

def MaxInNestedSeq (_ : List (List Int)) : Int := 0

def SubsegmentProfit (difficulties costs : List Int) (k : Int) (l r : Nat) : Int :=
  let length := r - l + 1
  let revenue := Int.ofNat length * k
  let costSum := SumRange costs l r
  let gap := if l = r then 0 else MaxGapSquared difficulties l r
  revenue - costSum - gap

def MaxSubsegmentProfit (difficulties costs : List Int) (k : Int) : Int :=
  if difficulties.length = 0 then 0
  else
    let allSegmentProfits := List.range difficulties.length |>.map (fun l =>
      List.range (difficulties.length - l) |>.map (fun len =>
        SubsegmentProfit difficulties costs k l (l + len)))
    IntMax 0 (MaxInNestedSeq allSegmentProfits)

def OptimalSegmentProfit (input : String) (n : Nat) (k : Int) : Int :=
  let lines := SplitLinesSpec input
  let difficulties := List.range n |>.map (fun i =>
    ParseIntSpec ((SplitWhitespaceSpec (lines[i + 1]!))[0]!))
  let costs := List.range n |>.map (fun i =>
    ParseIntSpec ((SplitWhitespaceSpec (lines[i + 1]!))[1]!))
  MaxSubsegmentProfit difficulties costs k

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length > 0 ∧ 
  result.data[(result.length - 1)]! = '\n' ∧
  (let lines := SplitLinesSpec input
   (lines.length = 0 ∨ lines.length = 1 ∨ 
    (SplitWhitespaceSpec (lines[0]!)).length < 2 ∨
    ParseIntSpec ((SplitWhitespaceSpec (lines[0]!))[0]!) ≤ 0) → 
   result = "0\n") ∧
  (ValidInput input →
   (let lines := SplitLinesSpec input
    let n := ParseIntSpec ((SplitWhitespaceSpec (lines[0]!))[0]!)
    let k := ParseIntSpec ((SplitWhitespaceSpec (lines[0]!))[1]!)
    ∃ profit, 
       profit ≥ 0 ∧ 
       result = IntToStringResult profit ++ "\n" ∧
       profit = OptimalSegmentProfit input (Int.natAbs n) k))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>