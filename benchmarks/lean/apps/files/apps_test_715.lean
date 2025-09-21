-- <vc-preamble>
def ValidResult (result : String) : Prop :=
  result ∈ ["A", "B", "C", "D"]

def ChoiceFromIndex (index : Int) : String :=
  if index = 0 then "A"
  else if index = 1 then "B"
  else if index = 2 then "C"
  else "D"

def SplitLines (s : String) : List String :=
  s.splitOn "\n"

def SortLengthsWithIndices (lengths : List Int) : List (Int × Int) :=
  let pairs := [(lengths[0]!, (0 : Int)), (lengths[1]!, (1 : Int)), (lengths[2]!, (2 : Int)), (lengths[3]!, (3 : Int))]
  pairs.mergeSort (fun a b => a.1 ≤ b.1)

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
  ValidResult result ∧
  (let lines := SplitLines input
   if lines.length < 4 then result = "C"
   else
     let lengths := [Int.ofNat (lines[0]!.length - 2), Int.ofNat (lines[1]!.length - 2), Int.ofNat (lines[2]!.length - 2), Int.ofNat (lines[3]!.length - 2)]
     let sortedPairs := SortLengthsWithIndices lengths
     let shortestTwiceShorter := (sortedPairs[0]!).1 * 2 ≤ (sortedPairs[1]!).1
     let longestTwiceLonger := (sortedPairs[3]!).1 ≥ (sortedPairs[2]!).1 * 2
     if shortestTwiceShorter ∧ longestTwiceLonger then result = "C"
     else if shortestTwiceShorter then result = ChoiceFromIndex (sortedPairs[0]!).2
     else if longestTwiceLonger then result = ChoiceFromIndex (sortedPairs[3]!).2
     else result = "C")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>