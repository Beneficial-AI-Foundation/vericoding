def problem_spec
-- function signature
(impl: Rat → Rat)
-- inputs
(number: Rat) :=
-- spec
let spec (res) :=
(0 : Rat) ≤ res ∧
res < (1 : Rat) ∧
↑(Int.floor number) + res = number;
number > (0 : Rat) →
-- program terminates
(∃ result, impl number = result ∧
-- return value satisfies spec
spec result)

def implementation (number: Rat) : Rat := number - ↑(Int.floor number)

-- LLM HELPER
lemma floor_le_self (x : Rat) : ↑(Int.floor x) ≤ x := by
  exact Int.floor_le x

-- LLM HELPER
lemma sub_floor_nonneg (x : Rat) : (0 : Rat) ≤ x - ↑(Int.floor x) := by
  rw [sub_nonneg]
  exact floor_le_self x

-- LLM HELPER
lemma sub_floor_lt_one (x : Rat) : x - ↑(Int.floor x) < (1 : Rat) := by
  rw [sub_lt_iff_lt_add]
  exact Int.lt_floor_add_one x

-- LLM HELPER
lemma floor_add_sub_floor (x : Rat) : ↑(Int.floor x) + (x - ↑(Int.floor x)) = x := by
  ring

theorem correctness
(number: Rat)
: problem_spec implementation number := by
  intro h
  use number - ↑(Int.floor number)
  constructor
  · rfl
  · constructor
    · exact sub_floor_nonneg number
    · constructor
      · exact sub_floor_lt_one number
      · exact floor_add_sub_floor number