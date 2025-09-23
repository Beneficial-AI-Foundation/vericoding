-- <vc-preamble>
def split_on_char (c : Char) (s : List Char) : List (List Char) :=
  sorry

def any (p : Char → Bool) (s : List Char) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shut_the_gate (farm : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_valid_chars (farm : String) :
  let result := shut_the_gate farm
  ∀ c ∈ result.data, c = 'H' ∨ c = 'R' ∨ c = 'C' ∨ c = 'A' ∨ c = 'V' ∨ 
                       c = '|' ∨ c = '/' ∨ c = '\\' ∨ c = '.' :=
  sorry

theorem preserves_gates (farm : String) :
  let result := shut_the_gate farm
  let gates := farm.data.enum.filter (fun p => p.2 = '|' ∨ p.2 = '/' ∨ p.2 = '\\')
  let result_gates := result.data.enum.filter (fun p => p.2 = '|' ∨ p.2 = '/' ∨ p.2 = '\\')
  gates = result_gates :=
  sorry

theorem enclosed_animals_stay (farm : String) :
  let result := shut_the_gate farm
  let sections := split_on_char '|' farm.data
  let result_sections := split_on_char '|' result.data
  sections.length ≥ 3 →
  ∀ i, 0 < i ∧ i < sections.length - 1 →
    (¬ any (fun c => c = '/' ∨ c = '\\') sections[i]!) →
    sections[i]! = result_sections[i]! :=
  sorry

theorem idempotent (farm : String) :
  let first_result := shut_the_gate farm
  shut_the_gate first_result = first_result :=
  sorry

/-
info: '|H|A|'
-/
-- #guard_msgs in
-- #eval shut_the_gate "|H|A|"

/-
info: './.'
-/
-- #guard_msgs in
-- #eval shut_the_gate "H/A"

/-
info: '|H/.|'
-/
-- #guard_msgs in
-- #eval shut_the_gate "|H/A|"
-- </vc-theorems>