-- <vc-preamble>
-- String operations and parsing functions (axiomatized for verification)
axiom SplitLines : String → List String
axiom ParseInt : String → IntResult
axiom ParseNames : List String → List (String × String)
axiom ParseIntSequence : String → IntSequenceResult
axiom CreateAllHandlePairs : List (String × String) → List (String × String)
axiom SortHandlePairs : List (String × String) → List (String × String)
axiom GreedyAssignmentWorks : List (String × String) → List Int → Int → Bool

structure IntResult where
  Valid : Bool
  Value : Int

structure IntSequenceResult where
  Valid : Bool
  Sequence : List Int

structure ParseResult where
  Valid : Bool
  n : Int
  names : List (String × String)
  permutation : List Int

axiom LexLess : String → String → Bool
axiom LexLessOrEqual : String → String → Bool

def AllNamesDistinct (names : List (String × String)) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < names.length ∧ 0 ≤ j ∧ j < names.length →
    (i ≠ j → names[i]!.1 ≠ names[j]!.1 ∧ names[i]!.1 ≠ names[j]!.2 ∧ 
             names[i]!.2 ≠ names[j]!.1 ∧ names[i]!.2 ≠ names[j]!.2)

axiom ParseInput : String → ParseResult

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  let parsed := ParseInput input
  parsed.Valid ∧ 
  parsed.n ≥ 1 ∧ 
  parsed.names.length = parsed.n.natAbs ∧
  parsed.permutation.length = parsed.n.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < parsed.n → 1 ≤ parsed.permutation[i.natAbs]! ∧ parsed.permutation[i.natAbs]! ≤ parsed.n) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < parsed.n → parsed.permutation[i.natAbs]! ≠ parsed.permutation[j.natAbs]!) ∧
  (∀ i, 0 ≤ i ∧ i < parsed.n → (parsed.names[i.natAbs]!).1.length > 0 ∧ (parsed.names[i.natAbs]!).2.length > 0) ∧
  AllNamesDistinct parsed.names

def CanAssignHandlesGreedy (input : String) : Prop :=
  input.length > 0 ∧
  ValidInput input ∧
  let parsed := ParseInput input
  let all_handles := CreateAllHandlePairs parsed.names
  let sorted_handles := SortHandlePairs all_handles
  GreedyAssignmentWorks sorted_handles parsed.permutation parsed.n

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ ValidInput stdin_input
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
  (result = "YES" ∨ result = "NO") ∧
  (result = "YES" ↔ CanAssignHandlesGreedy stdin_input)

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>