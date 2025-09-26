import Mathlib
-- <vc-preamble>
def split (s : String) (c : Char) : List String :=
  s.split (· = c)

def ValidInput (input : String) : Prop :=
  let lines := split input '\n'
  lines.length ≥ 2 ∧
  let O := lines[0]!
  let E := lines[1]!
  let a := O.length
  let b := E.length
  (a = b ∨ a = b + 1) ∧
  (a > 0 ∨ b = 0)

def GetO (input : String) : String :=
  (split input '\n')[0]!

def GetE (input : String) : String :=
  (split input '\n')[1]!

partial def InterleaveEqual (O E : String) : String :=
  if O.length = 0 then ""
  else String.mk [O.get 0, E.get 0] ++ InterleaveEqual (O.drop 1) (E.drop 1)

partial def InterleaveUnequal (O E : String) : String :=
  if E.length = 0 then O
  else String.mk [O.get 0, E.get 0] ++ InterleaveUnequal (O.drop 1) (E.drop 1)

def CorrectResult (input : String) : String :=
  let O := GetO input
  let E := GetE input
  let a := O.length
  let b := E.length
  if a = b then
    InterleaveEqual O E
  else
    InterleaveUnequal O E

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem CorrectResult_eq_equal_if_len_eq (O E : String) (h : O.length = E.length) :
    (if O.length = E.length then InterleaveEqual O E else InterleaveUnequal O E)
      = InterleaveEqual O E := by
  simp [h]

-- LLM HELPER
@[simp] theorem CorrectResult_eq_unequal_if_len_ne (O E : String) (h : O.length ≠ E.length) :
    (if O.length = E.length then InterleaveEqual O E else InterleaveUnequal O E)
      = InterleaveUnequal O E := by
  simp [h]

-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  CorrectResult input
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = CorrectResult input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  rfl
-- </vc-theorems>
