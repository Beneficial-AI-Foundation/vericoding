import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def sum_squares_helper (lst: List Rat) : Int :=
  match lst with
  | [] => 0
  | x :: xs => x.ceil^2 + sum_squares_helper xs

def implementation (lst: List Rat) : Int :=
  sum_squares_helper lst

-- LLM HELPER
lemma sum_squares_helper_empty : sum_squares_helper [] = 0 := by
  rfl

-- LLM HELPER
lemma sum_squares_helper_cons (x : Rat) (xs : List Rat) :
  sum_squares_helper (x :: xs) = x.ceil^2 + sum_squares_helper xs := by
  rfl

-- LLM HELPER
lemma list_drop_one_cons {α : Type*} (x : α) (xs : List α) :
  (x :: xs).drop 1 = xs := by
  rfl

-- LLM HELPER
lemma list_head_cons (x : Rat) (xs : List Rat) :
  (x :: xs)[0]! = x := by
  simp [List.get!]

def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(lst: List Rat) :=
-- spec
let spec (result: Int) :=
  (lst = [] → result = 0) ∧
  (lst != [] → 0 ≤ result - lst[0]!.ceil^2 ∧ (impl (lst.drop 1) = (result - lst[0]!.ceil^2)))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

theorem correctness
(lst: List Rat)
: problem_spec implementation lst := by
  unfold problem_spec implementation
  use sum_squares_helper lst
  constructor
  · rfl
  · unfold implementation
    cases' lst with x xs
    · simp [sum_squares_helper_empty]
    · constructor
      · intro h
        exfalso
        simp at h
      · intro h
        constructor
        · simp [sum_squares_helper_cons, list_head_cons]
          exact Int.zero_le_pow (x.ceil) 2
        · simp [list_drop_one_cons, list_head_cons, sum_squares_helper_cons]
          ring

-- #test implementation [1, 2, 3] = 14
-- #test implementation [1, 4, 9] = 98
-- #test implementation [1, 3, 5, 7] = 84
-- #test implementation [1.4, 4.2, 0] = 29
-- #test implementation [-2.4, 1, 1] = 6