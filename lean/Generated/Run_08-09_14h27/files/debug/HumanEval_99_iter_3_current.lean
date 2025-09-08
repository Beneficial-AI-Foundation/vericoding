/- 
function_signature: "def closest_integer(s : String) -> Option Int"
docstring: |
    Create a function that takes a value (string) representing a number
    and returns the closest integer to it. If the number is equidistant
    from two integers, round it away from zero.
test_cases:
  - input: "10"
    expected_output: 10
  - input: "15.3"
    expected_output: 15
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
import Std

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def parseNumber (s : String) : Option ℚ := 
  if s.isEmpty then none
  else
    let parts := s.split (fun c => c = '.')
    if parts.length = 1 then
      match s.toInt? with
      | some i => some (↑i)
      | none => none
    else if parts.length = 2 then
      match parts[0]!.toInt?, parts[1]!.toNat? with
      | some intPart, some fracPart =>
        let fracStr := parts[1]!
        if fracStr.isEmpty then none
        else
          let fracVal := (fracPart : ℚ) / (10 ^ fracStr.length : ℚ)
          if intPart ≥ 0 then
            some (intPart + fracVal)
          else
            some (intPart - fracVal)
      | _, _ => none
    else none

-- LLM HELPER  
def roundAwayFromZero (q : ℚ) : Int :=
  let floor_q := Int.floor q
  let ceil_q := Int.ceil q
  if floor_q = ceil_q then floor_q
  else
    let dist_to_floor := q - floor_q
    let dist_to_ceil := ceil_q - q
    if dist_to_floor < dist_to_ceil then floor_q
    else if dist_to_ceil < dist_to_floor then ceil_q
    else -- equidistant case
      if q ≥ 0 then ceil_q else floor_q

def implementation (s: String) : Option Int :=
  match parseNumber s with
  | some q => some (roundAwayFromZero q)
  | none => none

def problem_spec
-- function signature
(implementation: String → Option Int)
-- inputs
(s: String) :=
-- spec
let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
let is_valid_string :=
  s.length > 0 ∧
  s.count (".".get! 0) ≤ 1 ∧
  s.count ("-".get! 0) ≤ 1 ∧
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) ∧
  (s.count ("-".get! 0) = 1 → s.data.head! = '-')

let spec (result : Option Int) := match result with
  | some result =>
    is_valid_string ∧
    let parts := s.split (fun c => c = '.')
    (parts.length = 1 → result = s.toInt!) ∧
    (parts.length = 2 →
      let integer_part := parts[0]!
      let is_negative := s.data.head! = '-'
      |((integer_part.toInt! - result) : ℚ)| ≤ 0.5 ∧
      (is_negative → |((integer_part.toInt! - result) : ℚ)| = 0.5 → integer_part.toInt? < result) ∧
      (¬is_negative → |((integer_part.toInt! - result) : ℚ)| = 0.5 → integer_part.toInt? > result)
    )
  | none => ¬ is_valid_string
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
lemma implementation_terminates (s : String) : ∃ result, implementation s = result := by
  use implementation s
  rfl

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  obtain ⟨result, h_result⟩ := implementation_terminates s
  use result
  constructor
  · exact h_result
  · simp
    sorry

-- #test implementation "10" = some 10
-- #test implementation "15.3" = some 15