-- <vc-preamble>

structure ParseResult where
  Valid : Bool
  n : Nat
  names : List (String × String)
  permutation : List Nat

structure IntResult where
  Valid : Bool
  Value : Nat

structure IntSequenceResult where
  Valid : Bool
  Sequence : List Nat

noncomputable axiom SplitLines : String → List String
axiom ParseInt : String → IntResult
axiom ParseNames : List String → List (String × String)
axiom ParseIntSequence : String → IntSequenceResult
axiom CreateAllHandlePairs : List (String × String) → List (String × String)
axiom SortHandlePairs : List (String × String) → List (String × String)
axiom GreedyAssignmentWorks : List (String × String) → List Nat → Nat → Prop

noncomputable def ParseInput (input : String) : ParseResult :=
  if input.length = 0 then ParseResult.mk false 0 [] []
  else
    let lines := SplitLines input
    if lines.length < 2 then ParseResult.mk false 0 [] []
    else
      let n_result := ParseInt (lines.get! 0)
      if ¬n_result.Valid ∨ n_result.Value ≤ 0 ∨ lines.length ≠ n_result.Value + 2
      then ParseResult.mk false 0 [] []
      else
        let names := ParseNames ((lines.drop 1).take n_result.Value)
        let perm := ParseIntSequence (lines.get! (n_result.Value + 1))
        if names.length = n_result.Value ∧ perm.Valid ∧ perm.Sequence.length = n_result.Value
        then ParseResult.mk true n_result.Value names perm.Sequence
        else ParseResult.mk false 0 [] []

def AllNamesDistinct (names : List (String × String)) : Prop :=
  ∀ i j, i < names.length ∧ j < names.length →
    (i ≠ j → (names.get! i).1 ≠ (names.get! j).1 ∧ (names.get! i).1 ≠ (names.get! j).2 ∧ 
             (names.get! i).2 ≠ (names.get! j).1 ∧ (names.get! i).2 ≠ (names.get! j).2)

noncomputable def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  let parsed := ParseInput input
  parsed.Valid ∧ 
  parsed.n ≥ 1 ∧ 
  parsed.names.length = parsed.n ∧
  parsed.permutation.length = parsed.n ∧
  (∀ i, i < parsed.n → 1 ≤ (parsed.permutation.get! i) ∧ (parsed.permutation.get! i) ≤ parsed.n) ∧
  (∀ i j, i < j ∧ j < parsed.n → (parsed.permutation.get! i) ≠ (parsed.permutation.get! j)) ∧
  (∀ i, i < parsed.n → (parsed.names.get! i).1.length > 0 ∧ (parsed.names.get! i).2.length > 0) ∧
  AllNamesDistinct parsed.names

noncomputable def CanAssignHandlesGreedy (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input ∧
  let parsed := ParseInput input
  let all_handles := CreateAllHandlePairs parsed.names
  let sorted_handles := SortHandlePairs all_handles
  GreedyAssignmentWorks sorted_handles parsed.permutation parsed.n

def LexLess : String → String → Bool := sorry

def LexLessOrEqual (a b : String) : Bool :=
  LexLess a b ∨ a = b

@[reducible, simp]
noncomputable def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
noncomputable def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  (result = "YES" ∨ result = "NO") ∧
  (result = "YES" ↔ CanAssignHandlesGreedy stdin_input)

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>
