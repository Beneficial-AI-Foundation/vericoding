-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def interpreter (code: String) (tape: String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_code_unchanged (tape: String) (h: ∀ c, c ∈ tape.data → c = '0' ∨ c = '1') : 
  interpreter "" tape = tape :=
  sorry

theorem output_is_binary (code tape result: String)
  (h: ∀ c, c ∈ tape.data → c = '0' ∨ c = '1')
  (h2: result = interpreter code tape) :
  (∀ c, c ∈ result.data → c = '0' ∨ c = '1') ∧ result.length = tape.length :=
  sorry

theorem single_flip_inverts (tape: String) 
  (h: tape.length > 0)
  (h2: ∀ c, c ∈ tape.data → c = '0' ∨ c = '1') :
  let result := interpreter "*" tape
  let first_char := tape.get 0
  let new_first_char := result.get 0
  (first_char = '0' → new_first_char = '1') ∧
  (first_char = '1' → new_first_char = '0') ∧
  result.drop 1 = tape.drop 1 :=
  sorry

theorem pointer_bounds (code tape: String)
  (h: ∀ c, c ∈ tape.data → c = '0' ∨ c = '1') :
  (interpreter code tape).length = tape.length :=
  sorry
-- </vc-theorems>