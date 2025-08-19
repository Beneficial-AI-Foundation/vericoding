-- LLM HELPER
def is_digit (c : Char) : Bool :=
  c >= '0' && c <= '9'

-- LLM HELPER
def is_valid_numeric_string (s : String) : Bool :=
  let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
  s.length > 0 &&
  s.count (".".get! 0) ≤ 1 &&
  s.count ("-".get! 0) ≤ 1 &&
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) &&
  (s.count ("-".get! 0) = 1 → s.data.head! = '-')

-- LLM HELPER
def round_to_nearest_int (q : ℚ) : Int :=
  let floor_q := Int.floor q
  let frac := q - floor_q
  if frac < 1/2 then floor_q
  else if frac > 1/2 then floor_q + 1
  else -- frac = 1/2, round to even
    if floor_q % 2 = 0 then floor_q else floor_q + 1

-- LLM HELPER
def parse_decimal (s : String) : Option ℚ :=
  let parts := s.split (fun c => c = '.')
  if parts.length = 1 then
    match s.toInt? with
    | some n => some n
    | none => none
  else if parts.length = 2 then
    let integer_part := parts.get! 0
    let decimal_part := parts.get! 1
    match integer_part.toInt?, decimal_part.toNat? with
    | some int_val, some dec_val =>
      let dec_places := decimal_part.length
      let decimal_fraction : ℚ := dec_val / (10 ^ dec_places)
      if int_val >= 0 then
        some (int_val + decimal_fraction)
      else
        some (int_val - decimal_fraction)
    | _, _ => none
  else none

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
      let integer_part := parts.get! 0
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

def implementation (s: String) : Option Int :=
  if is_valid_numeric_string s then
    match parse_decimal s with
    | some q => some (round_to_nearest_int q)
    | none => none
  else
    none

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  sorry