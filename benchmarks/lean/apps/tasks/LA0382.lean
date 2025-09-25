-- <vc-preamble>
-- Helper functions (assumed to exist)
axiom split_lines : String → List String
axiom parse_int : String → Int
noncomputable axiom reverse_string : String → String

def ValidInput (s : String) : Prop :=
  s.length ≥ 2 ∧
  (s.data[s.length - 1]! = '\n' ∨ (s.length ≥ 2 ∧ s.drop (s.length - 2) = "\n")) ∧
  (∃ lines, lines = split_lines s ∧ lines.length ≥ 1) ∧
  (∃ lines t, lines = split_lines s ∧ t = parse_int (lines[0]!) ∧ t ≥ 1) ∧
  (∀ lines t, (lines = split_lines s ∧ t = parse_int (lines[0]!)) → lines.length ≥ 1 + 2 * t.natAbs) ∧
  (∀ lines t i, (lines = split_lines s ∧ t = parse_int (lines[0]!) ∧ 0 ≤ i ∧ i < t) → 
    (∃ n, n = parse_int (lines[(1 + 2 * i).natAbs]!) ∧ n ≥ 1 ∧ n ≤ 5000 ∧ (lines[(1 + 2 * i + 1).natAbs]!).length = n.natAbs)) ∧
  (∀ lines t i, (lines = split_lines s ∧ t = parse_int (lines[0]!) ∧ 0 ≤ i ∧ i < t) → 
    (∀ j, 0 ≤ j ∧ j < (lines[(1 + 2 * i + 1).natAbs]!).length → 
      (lines[(1 + 2 * i + 1).natAbs]!).data[j]! ∈ "abcdefghijklmnopqrstuvwxyz".data))

def ValidOutput (result : String) : Prop :=
  result.length ≥ 0 ∧
  (result = "" ∨ result.data[result.length - 1]! = '\n')

noncomputable def transform_string (input_str : String) (n : Int) (k : Int) : String :=
  if h : 1 ≤ k ∧ k ≤ n ∧ input_str.length = n.natAbs then
    let i := k - 1
    if (n - i) % 2 = 0 then
      input_str.drop i.natAbs ++ input_str.take i.natAbs
    else
      input_str.drop i.natAbs ++ reverse_string (input_str.take i.natAbs)
  else
    ""

def is_lexicographically_optimal (result_str : String) (input_str : String) (n : Int) (k : Int) : Prop :=
  input_str.length = n.natAbs →
  (1 ≤ k ∧ k ≤ n ∧
   (∃ transformation, transformation = transform_string input_str n k ∧ result_str = transformation ∧
    ∀ other_k, 1 ≤ other_k ∧ other_k ≤ n → result_str ≤ transform_string input_str n other_k))

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  ValidOutput result

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>