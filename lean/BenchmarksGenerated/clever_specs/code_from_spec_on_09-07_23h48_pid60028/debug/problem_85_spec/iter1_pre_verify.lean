def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Int) :=
  lst.length = 0 → result = 0 ∧
  lst.length > 0 →
    if lst.length > 1 then
      result = (if Even lst[1]! then lst[1]! else 0) + implementation (lst.drop 2)
    else
      result = (if Even lst[1]! then lst[1]! else 0)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

def implementation (lst: List Int) : Int :=
  match lst with
  | [] => 0
  | [_] => 0
  | _ :: x :: xs => (if Even x then x else 0) + implementation xs

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  exists implementation lst
  constructor
  · rfl
  · constructor
    · intro h
      cases lst with
      | nil => rfl
      | cons head tail =>
        simp at h
    · intro h
      cases lst with
      | nil => 
        simp at h
      | cons head tail =>
        cases tail with
        | nil =>
          simp [implementation]
          rfl
        | cons second rest =>
          simp [implementation]
          rfl