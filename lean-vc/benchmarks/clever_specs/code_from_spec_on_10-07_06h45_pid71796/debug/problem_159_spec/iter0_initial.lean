import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → Nat → Nat → List Nat)
-- inputs
(number need remaining: Nat) :=
-- spec
let spec (result: List Nat) :=
number ≤ 1000 → need ≤ 1000 → remaining ≤ 1000 →
result.length = 2 ∧
(need ≤ remaining → result[0]! - need = number ∧
need = remaining - result[1]!) ∧
(remaining < need → result[0]! - remaining = number ∧
result[1]! = 0);
-- program terminates
∃ result, impl number need remaining = result ∧
-- return value satisfies spec
spec result

def implementation (a b c: Nat) : List Nat := 
  if b ≤ c then
    [a + b, c - b]
  else
    [a + c, 0]

-- LLM HELPER
lemma list_get_elem_two_elems (x y : Nat) : 
  ([x, y] : List Nat)[0]! = x ∧ ([x, y] : List Nat)[1]! = y := by
  simp [List.get_elem!]

-- LLM HELPER
lemma list_length_two_elems (x y : Nat) : 
  ([x, y] : List Nat).length = 2 := by
  simp

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  unfold problem_spec
  unfold implementation
  simp only [exists_prop]
  split_ifs with h
  · -- Case: b ≤ c
    use [a + b, c - b]
    constructor
    · rfl
    · intro ha hb hc
      constructor
      · exact list_length_two_elems (a + b) (c - b)
      · constructor
        · intro h_need_le_remaining
          constructor
          · have h1 := list_get_elem_two_elems (a + b) (c - b)
            rw [h1.1]
            simp [Nat.add_sub_cancel]
          · have h2 := list_get_elem_two_elems (a + b) (c - b)
            rw [h2.2]
            exact Nat.add_sub_cancel c b
        · intro h_remaining_lt_need
          exfalso
          exact not_lt.mpr h h_remaining_lt_need
  · -- Case: ¬(b ≤ c), i.e., c < b
    use [a + c, 0]
    constructor
    · rfl
    · intro ha hb hc
      constructor
      · exact list_length_two_elems (a + c) 0
      · constructor
        · intro h_need_le_remaining
          exfalso
          exact h h_need_le_remaining
        · intro h_remaining_lt_need
          constructor
          · have h1 := list_get_elem_two_elems (a + c) 0
            rw [h1.1]
            simp [Nat.add_sub_cancel]
          · have h2 := list_get_elem_two_elems (a + c) 0
            exact h2.2