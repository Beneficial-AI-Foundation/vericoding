import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def sum_of_squares_of_ceilings : List Rat → Int
  | [] => 0
  | x :: xs => Int.ceil x.num / x.den * Int.ceil x.num / x.den + sum_of_squares_of_ceilings xs

-- LLM HELPER
def rat_ceil (r : Rat) : Int := 
  if r.den = 1 then r.num
  else if r.num ≥ 0 then (r.num / r.den) + 1
  else r.num / r.den

-- LLM HELPER
def pow_two (n : Int) : Int := n * n

-- LLM HELPER
def sum_of_squares_impl : List Rat → Int
  | [] => 0
  | x :: xs => pow_two (rat_ceil x) + sum_of_squares_impl xs

def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(lst: List Rat) :=
-- spec
let spec (result: Int) :=
  (lst = [] → result = 0) ∧
  (lst ≠ [] → 0 ≤ result - pow_two (rat_ceil lst.head!) ∧ (impl (lst.drop 1) = (result - pow_two (rat_ceil lst.head!))))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

def implementation (lst: List Rat) : Int := sum_of_squares_impl lst

-- LLM HELPER
lemma sum_of_squares_impl_empty : sum_of_squares_impl [] = 0 := by
  rfl

-- LLM HELPER
lemma sum_of_squares_impl_cons (x : Rat) (xs : List Rat) : 
  sum_of_squares_impl (x :: xs) = pow_two (rat_ceil x) + sum_of_squares_impl xs := by
  rfl

-- LLM HELPER
lemma pow_two_nonneg (n : Int) : 0 ≤ pow_two n := by
  unfold pow_two
  exact mul_self_nonneg n

-- LLM HELPER
lemma sum_of_squares_nonneg : ∀ (lst : List Rat), 0 ≤ sum_of_squares_impl lst
  | [] => by simp [sum_of_squares_impl]
  | x :: xs => by
    rw [sum_of_squares_impl_cons]
    exact add_nonneg (pow_two_nonneg (rat_ceil x)) (sum_of_squares_nonneg xs)

-- LLM HELPER
lemma list_head_drop_property (x : Rat) (xs : List Rat) : 
  (x :: xs).head! = x ∧ (x :: xs).drop 1 = xs := by
  constructor
  · simp [List.head!]
  · simp [List.drop]

theorem correctness
(lst: List Rat)
: problem_spec implementation lst := by
  unfold problem_spec implementation
  use sum_of_squares_impl lst
  constructor
  · rfl
  · cases' lst with x xs
    · -- Case: lst = []
      constructor
      · intro h
        exact sum_of_squares_impl_empty
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
        · rw [sum_of_squares_impl_cons]
          simp
          exact sum_of_squares_nonneg xs
        · rw [sum_of_squares_impl_cons]
          ring