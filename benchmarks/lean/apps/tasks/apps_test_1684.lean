-- <vc-preamble>
structure InputData where
  n : Int
  m : Int
  segments : List (Int × Int)

def valid_input_format (stdin_input : String) : Prop :=
  stdin_input.length > 0

def parse_input (stdin_input : String) : InputData :=
  { n := 2, m := 0, segments := [] }

def rotate_segment (seg : Int × Int) (k : Int) (n : Int) : Int × Int :=
  let temp_a := (seg.1 + k) % n
  let a := if temp_a = 0 then n else temp_a
  let temp_b := (seg.2 + k) % n
  let b := if temp_b = 0 then n else temp_b
  (a, b)

def exists_rotational_symmetry (data : InputData) : Prop :=
  ∃ k, 1 ≤ k ∧ k < data.n ∧ 
       data.n % k = 0 ∧
       (∀ seg ∈ data.segments, 
           seg.1 ≥ 1 ∧ seg.1 ≤ data.n ∧ seg.2 ≥ 1 ∧ seg.2 ≤ data.n ∧
           rotate_segment seg k data.n ∈ data.segments)

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ valid_input_format stdin_input
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
  (result = "Yes" ∨ result = "No") ∧ 
  (result = "Yes" ↔ exists_rotational_symmetry (parse_input stdin_input))

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>