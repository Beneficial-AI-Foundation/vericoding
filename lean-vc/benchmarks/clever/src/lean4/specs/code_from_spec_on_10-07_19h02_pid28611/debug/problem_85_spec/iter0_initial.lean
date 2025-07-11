import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

-- LLM HELPER
lemma list_length_cases (lst : List Int) : 
  lst.length = 0 ∨ (lst.length = 1 ∧ ∃ a, lst = [a]) ∨ (lst.length > 1 ∧ ∃ a b xs, lst = a :: b :: xs) := by
  cases lst with
  | nil => left; simp
  | cons a as =>
    cases as with
    | nil => right; left; simp; use a
    | cons b bs => right; right; simp; use a, b, bs

-- LLM HELPER
lemma drop_two_length (lst : List Int) : lst.length ≥ 2 → (lst.drop 2).length < lst.length := by
  intro h
  simp [List.length_drop]
  omega

-- LLM HELPER  
lemma get_second_element (a b : Int) (xs : List Int) : (a :: b :: xs)[1]! = b := by
  simp [List.get_cons_succ]

-- LLM HELPER
lemma drop_two_cons (a b : Int) (xs : List Int) : (a :: b :: xs).drop 2 = xs := by
  simp [List.drop]

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  unfold problem_spec
  simp only [exists_prop]
  constructor
  · rfl
  · intro spec
    intro h
    cases' list_length_cases lst with h1 h2
    · -- Case: lst.length = 0
      rw [h1] at h
      contradiction
    · cases' h2 with h2 h3
      · -- Case: lst.length = 1
        obtain ⟨a, ha⟩ := h2.2
        rw [ha]
        simp [implementation]
        rw [ha] at h2
        simp at h2
        rw [h2.1]
        simp
      · -- Case: lst.length > 1
        obtain ⟨a, b, xs, hxs⟩ := h3.2
        rw [hxs]
        simp [implementation]
        rw [hxs] at h3
        simp at h3
        rw [if_pos h3.1]
        rw [hxs]
        simp
        rw [get_second_element, drop_two_cons]