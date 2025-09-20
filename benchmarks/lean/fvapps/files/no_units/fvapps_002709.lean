-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greet_jedi (first last : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greet_jedi_starts_with_prefix (first last : String) :
  (greet_jedi first last).startsWith "Greetings, master " = true :=
  sorry

theorem greet_jedi_name_part_nonempty (first last : String) :
  (first.length ≥ 2) → (last.length ≥ 2) →
  let result := greet_jedi first last
  let name_part := result.replace "Greetings, master " ""
  name_part.length ≥ 1 :=
  sorry

theorem greet_jedi_name_part_bounded (first last : String) : 
  (first.length ≥ 2) → (last.length ≥ 2) →
  let result := greet_jedi first last
  let name_part := result.replace "Greetings, master " ""
  name_part.length ≤ 5 :=
  sorry
-- </vc-theorems>