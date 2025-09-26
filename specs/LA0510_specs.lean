-- <vc-preamble>
def TrimNewlines (s : String) : String := s.trimRight

def FindSpace (s : String) : Int := 
  let rec findHelper (chars : List Char) (index : Nat) : Int :=
    match chars with
    | [] => -1
    | c :: cs => if c = ' ' then index else findHelper cs (index + 1)
  findHelper s.toList 0

def StringToInt (s : String) : Int := 
  s.toInt?.getD 0

def IsValidInteger (s : String) : Prop := True

def ValidInputFormat (input : String) : Prop :=
  let trimmed := TrimNewlines input
  let spaceIndex := FindSpace trimmed
  spaceIndex ≥ 0 ∧ spaceIndex < Int.ofNat trimmed.length - 1 ∧
  IsValidInteger (trimmed.take spaceIndex.natAbs) ∧
  IsValidInteger (trimmed.drop (spaceIndex.natAbs + 1))

def ValidInput (input : String) (S W : Int) : Prop :=
  ValidInputFormat input ∧
  let trimmed := TrimNewlines input
  let spaceIndex := FindSpace trimmed
  let sStr := trimmed.take spaceIndex.natAbs
  let wStr := trimmed.drop (spaceIndex.natAbs + 1)
  StringToInt sStr = S ∧ StringToInt wStr = W

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
  (result = "safe\n" ∨ result = "unsafe\n" ∨ result = "") ∧
  (ValidInputFormat input → 
    let trimmed := TrimNewlines input
    let spaceIndex := FindSpace trimmed
    let S := StringToInt (trimmed.take spaceIndex.natAbs)
    let W := StringToInt (trimmed.drop (spaceIndex.natAbs + 1))
    (W < S → result = "safe\n") ∧ (W ≥ S → result = "unsafe\n")) ∧
  (¬ValidInputFormat input → result = "")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>