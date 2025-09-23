-- <vc-preamble>
def splitLines (s : String) : List String := s.splitOn "\n"

def parseInt (s : String) : Int := s.toInt!

def isValidPositiveInteger (s : String) : Prop :=
  s.length ≥ 1 ∧
  (∀ i : Nat, i < s.length →
      let c := s.data[i]!
      c ≥ '0' ∧ c ≤ '9') ∧
  (s.length = 1 ∨ s.data[0]! ≠ '0')

def isLexicographicallySmaller (a : String) (b : String) : Prop :=
  isValidPositiveInteger a ∧ isValidPositiveInteger b →
  (a.length < b.length ∨ (a.length = b.length ∧ a < b))

def isStrictlyIncreasingSequence (nums : List String) : Prop :=
  (∀ i : Nat, i < nums.length → isValidPositiveInteger (nums[i]!)) →
  (∀ i : Nat, i < nums.length - 1 → isLexicographicallySmaller (nums[i]!) (nums[i + 1]!))

def isValidSequenceSolution (input : List String) (solution : List String) : Prop :=
  input.length = solution.length ∧
  (∀ i : Nat, i < input.length →
      let inp := input[i]!
      let sol := solution[i]!
      inp.length = sol.length ∧
      ∀ j : Nat, j < inp.length →
          let inp_char := inp.data[j]!
          let sol_char := sol.data[j]!
          (inp_char ≠ '?' → inp_char = sol_char) ∧
          (inp_char = '?' → sol_char ≥ '0' ∧ sol_char ≤ '9')) ∧
  (∀ i : Nat, i < solution.length → isValidPositiveInteger (solution[i]!)) ∧
  isStrictlyIncreasingSequence solution

def isWellFormedInput (stdin_input : String) : Prop :=
  let lines := splitLines stdin_input
  if lines.length < 1 then False
  else
    let n := parseInt (lines[0]!)
    n ≥ 0 ∧ Int.natAbs lines.length ≥ Int.natAbs n + 1 ∧
    (∀ i : Nat, 1 ≤ i ∧ Int.ofNat i ≤ n ∧ i < lines.length →
        let line := lines[i]!
        line.length ≥ 1 ∧ line.length ≤ 8 ∧
        (∀ j : Nat, j < line.length →
            let c := line.data[j]!
            (c ≥ '0' ∧ c ≤ '9') ∨ c = '?'))

def hasValidSolution (stdin_input : String) : Prop :=
  let lines := splitLines stdin_input
  let n := parseInt (lines[0]!)
  if n ≤ 0 then True
  else
    let inputStrings := lines.drop 1 |>.take (Int.natAbs n)
    ∃ solution, isValidSequenceSolution inputStrings solution

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ isWellFormedInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result.length > 0 ∧
  (result = "NO\n" ∨ (result.length > 4 ∧ result.take 4 = "YES\n"))

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>