import Mathlib
-- <vc-preamble>
def reverse (s : String) : String :=
  s.data.reverse.asString

def split_lines (s : String) : List String :=
  s.splitOn "\n"

def ValidInput (lines : List String) : Prop :=
  lines.length ≥ 2 ∧ lines[0]!.length > 0 ∧ lines[1]!.length > 0

def IsSymmetric (first_row second_row : String) : Prop :=
  reverse first_row = second_row

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0
-- </vc-preamble>

-- <vc-helpers>
instance (s1 s2 : String) : Decidable (IsSymmetric s1 s2) := by
  unfold IsSymmetric
  infer_instance

instance (lines : List String) : Decidable (ValidInput lines) :=
  if h_len_ge_2 : lines.length ≥ 2 then
    if h0 : (lines[0]!).length > 0 then
      if h1 : (lines[1]!).length > 0 then
        isTrue ⟨h_len_ge_2, ⟨h0, h1⟩⟩
      else
        isFalse (fun h' => h1 h'.2.2)
    else
      isFalse (fun h' => h0 h'.2.1)
  else
    isFalse (fun h' => h_len_ge_2 h'.1)
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  let normalized_input := stdin_input ++ (if stdin_input.back = '\n' then "" else "\n")
  let lines := split_lines normalized_input
  if h : ValidInput lines then
    if IsSymmetric lines[0]! lines[1]! then
      "YES\n"
    else
      "NO\n"
  else
    "NO\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  (result = "YES\n" ∨ result = "NO\n") ∧
  (let normalized_input := stdin_input ++ (if stdin_input.back = '\n' then "" else "\n")
   let lines := split_lines normalized_input
   ValidInput lines → (result = "YES\n" ↔ IsSymmetric lines[0]! lines[1]!)) ∧
  (let normalized_input := stdin_input ++ (if stdin_input.back = '\n' then "" else "\n")
   let lines := split_lines normalized_input
   ¬ValidInput lines → result = "NO\n")

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  unfold solve solve_postcond
  dsimp
  split_ifs <;> simp_all
-- </vc-theorems>
