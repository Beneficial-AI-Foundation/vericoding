import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

-- LLM HELPER
def sum_of_squares_of_ceilings : List Rat → Int
  | [] => 0
  | x :: xs => x.ceil^2 + sum_of_squares_of_ceilings xs

def implementation (lst: List Rat) : Int := sum_of_squares_of_ceilings lst

-- LLM HELPER
lemma sum_of_squares_of_ceilings_empty : sum_of_squares_of_ceilings [] = 0 := by
  rfl

-- LLM HELPER
lemma sum_of_squares_of_ceilings_cons (x : Rat) (xs : List Rat) : 
  sum_of_squares_of_ceilings (x :: xs) = x.ceil^2 + sum_of_squares_of_ceilings xs := by
  rfl

-- LLM HELPER
lemma pow_two_nonneg (n : Int) : 0 ≤ n^2 := by
  exact sq_nonneg n

-- LLM HELPER
lemma sum_of_squares_nonneg : ∀ (lst : List Rat), 0 ≤ sum_of_squares_of_ceilings lst
  | [] => by simp [sum_of_squares_of_ceilings]
  | x :: xs => by
    rw [sum_of_squares_of_ceilings_cons]
    exact add_nonneg (pow_two_nonneg x.ceil) (sum_of_squares_nonneg xs)

-- LLM HELPER
lemma list_nonempty_iff_ne_nil {α : Type*} (lst : List α) : lst ≠ [] ↔ lst.length > 0 := by
  constructor
  · intro h
    cases' lst with hd tl
    · contradiction
    · simp
  · intro h
    cases' lst with hd tl
    · simp at h
    · simp

-- LLM HELPER
lemma list_head_drop_property (x : Rat) (xs : List Rat) : 
  (x :: xs)[0]! = x ∧ (x :: xs).drop 1 = xs := by
  constructor
  · simp [List.get!]
  · simp [List.drop]

theorem correctness
(lst: List Rat)
: problem_spec implementation lst := by
  unfold problem_spec implementation
  use sum_of_squares_of_ceilings lst
  constructor
  · rfl
  · unfold problem_spec
    cases' lst with x xs
    · -- Case: lst = []
      constructor
      · intro h
        exact sum_of_squares_of_ceilings_empty
      · intro h
        simp at h
    · -- Case: lst = x :: xs
      constructor
      · intro h
        simp at h
      · intro h
        have h_head_drop := list_head_drop_property x xs
        rw [h_head_drop.1, h_head_drop.2]
        constructor
        · rw [sum_of_squares_of_ceilings_cons]
          simp
          exact sum_of_squares_nonneg xs
        · rw [sum_of_squares_of_ceilings_cons]
          ring