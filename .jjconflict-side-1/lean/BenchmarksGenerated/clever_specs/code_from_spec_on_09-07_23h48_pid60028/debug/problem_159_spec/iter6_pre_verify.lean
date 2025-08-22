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
lemma list_length_two (a b : Nat) : [a, b].length = 2 := by simp

-- LLM HELPER
lemma list_get_zero (a b : Nat) : [a, b][0]! = a := by simp

-- LLM HELPER
lemma list_get_one (a b : Nat) : [a, b][1]! = b := by simp

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  simp [problem_spec]
  use implementation a b c
  constructor
  · rfl
  · intro ha hb hc
    simp [implementation]
    constructor
    · split_ifs <;> simp [list_length_two]
    · constructor
      · intro h
        simp [if_pos h]
        constructor
        · simp [list_get_zero]
          omega
        · simp [list_get_one]
          omega
      · intro h
        simp [if_neg (not_le.mpr h)]
        constructor
        · simp [list_get_zero]
          omega
        · simp [list_get_one]