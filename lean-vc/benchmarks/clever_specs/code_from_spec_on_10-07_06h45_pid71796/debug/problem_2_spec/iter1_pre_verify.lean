def problem_spec
-- function signature
(impl: Rat → Rat)
-- inputs
(number: Rat) :=
-- spec
let spec (res) :=
0 ≤ res ∧
res < 1 ∧
number.floor + res = number;
number > 0 →
-- program terminates
(∃ result, impl number = result ∧
-- return value satisfies spec
spec result)

def implementation (number: Rat) : Rat := number - number.floor

-- LLM HELPER
lemma floor_le_self (x : Rat) : x.floor ≤ x := by
  exact Int.floor_le x

-- LLM HELPER
lemma self_lt_floor_add_one (x : Rat) : x < x.floor + 1 := by
  exact Int.lt_floor_add_one x

-- LLM HELPER
lemma sub_floor_nonneg (x : Rat) : 0 ≤ x - x.floor := by
  simp only [sub_nonneg]
  exact floor_le_self x

-- LLM HELPER
lemma sub_floor_lt_one (x : Rat) : x - x.floor < 1 := by
  have h : x < x.floor + 1 := self_lt_floor_add_one x
  linarith

-- LLM HELPER
lemma floor_add_sub_floor (x : Rat) : x.floor + (x - x.floor) = x := by
  ring

theorem correctness
(number: Rat)
: problem_spec implementation number := by
  unfold problem_spec
  intro h_pos
  use number - number.floor
  constructor
  · rfl
  · constructor
    · exact sub_floor_nonneg number
    · constructor
      · exact sub_floor_lt_one number
      · exact floor_add_sub_floor number