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
  simp

-- LLM HELPER
lemma square_nonneg (n : Int) : 0 ≤ n^2 := by
  by_cases h : 0 ≤ n
  · exact sq_nonneg n
  · have : n < 0 := not_le.mp h
    have : n^2 = (-n)^2 := by simp
    rw [this]
    exact sq_nonneg (-n)

-- LLM HELPER
lemma sum_squares_helper_nonneg (xs : List Rat) : 0 ≤ sum_squares_helper xs := by
  induction' xs with x xs' ih
  · simp [sum_squares_helper_empty]
  · simp [sum_squares_helper_cons]
    apply add_nonneg
    · exact square_nonneg x.ceil
    · exact ih

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
  unfold problem_spec
  use sum_squares_helper lst
  constructor
  · rfl
  · cases' lst with x xs
    · constructor
      · intro h
        rfl
      · intro h
        exfalso
        exact h rfl
    · constructor
      · intro h
        exfalso
        simp at h
      · intro h
        constructor
        · simp [sum_squares_helper_cons]
          exact sum_squares_helper_nonneg xs
        · rw [sum_squares_helper_cons]
          rfl

-- #test implementation [1, 2, 3] = 14
-- #test implementation [1, 4, 9] = 98
-- #test implementation [1, 3, 5, 7] = 84
-- #test implementation [1.4, 4.2, 0] = 29
-- #test implementation [-2.4, 1, 1] = 6