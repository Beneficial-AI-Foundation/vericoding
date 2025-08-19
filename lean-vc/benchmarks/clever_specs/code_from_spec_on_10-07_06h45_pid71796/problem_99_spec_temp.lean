-- LLM HELPER
def is_digit (c : Char) : Bool :=
  c >= '0' && c <= '9'

-- LLM HELPER
def count_char (s : String) (c : Char) : Nat :=
  s.data.filter (· = c) |>.length

-- LLM HELPER
def is_valid_numeric_string (s : String) : Bool :=
  let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
  s.length > 0 &&
  count_char s '.' ≤ 1 &&
  count_char s '-' ≤ 1 &&
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) &&
  (count_char s '-' = 1 → s.data.head! = '-')

-- LLM HELPER
def floor_rat (q : ℚ) : ℤ :=
  Int.floor q

-- LLM HELPER
def round_to_nearest_int (q : ℚ) : ℤ :=
  let floor_q := floor_rat q
  let frac := q - floor_q
  if frac < (1 : ℚ) / 2 then floor_q
  else if frac > (1 : ℚ) / 2 then floor_q + 1
  else -- frac = 1/2, round to even
    if floor_q % 2 = 0 then floor_q else floor_q + 1

-- LLM HELPER
def parse_decimal (s : String) : Option ℚ :=
  let parts := s.split (fun c => c = '.')
  if parts.length = 1 then
    match s.toInt? with
    | some n => some (n : ℚ)
    | none => none
  else if parts.length = 2 then
    let integer_part := parts[0]!
    let decimal_part := parts[1]!
    match integer_part.toInt?, decimal_part.toNat? with
    | some int_val, some dec_val =>
      let dec_places := decimal_part.length
      let decimal_fraction : ℚ := (dec_val : ℚ) / ((10 ^ dec_places) : ℚ)
      if int_val >= 0 then
        some ((int_val : ℚ) + decimal_fraction)
      else
        some ((int_val : ℚ) - decimal_fraction)
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
  count_char s '.' ≤ 1 ∧
  count_char s '-' ≤ 1 ∧
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) ∧
  (count_char s '-' = 1 → s.data.head! = '-')

let spec (result : Option Int) := match result with
  | some result =>
    is_valid_string ∧
    let parts := s.split (fun c => c = '.')
    (parts.length = 1 → result = s.toInt!) ∧
    (parts.length = 2 →
      let integer_part := parts[0]!
      let is_negative := s.data.head! = '-'
      abs ((integer_part.toInt! : ℚ) - (result : ℚ)) ≤ (1 : ℚ) / 2 ∧
      (is_negative → abs ((integer_part.toInt! : ℚ) - (result : ℚ)) = (1 : ℚ) / 2 → integer_part.toInt! < result) ∧
      (¬is_negative → abs ((integer_part.toInt! : ℚ) - (result : ℚ)) = (1 : ℚ) / 2 → integer_part.toInt! > result)
    )
  | none => ¬ is_valid_string
-- program termination
∃ result,
  implementation s = result ∧
  spec result

def implementation (s: String) : Option Int :=
  if is_valid_numeric_string s then
    let parts := s.split (fun c => c = '.')
    if parts.length = 1 then
      some s.toInt!
    else if parts.length = 2 then
      let integer_part := parts[0]!
      let decimal_part := parts[1]!
      match integer_part.toInt?, decimal_part.toNat? with
      | some int_val, some dec_val =>
        let dec_places := decimal_part.length
        let decimal_fraction : ℚ := (dec_val : ℚ) / ((10 ^ dec_places) : ℚ)
        let full_rat : ℚ := if int_val >= 0 then
          (int_val : ℚ) + decimal_fraction
        else
          (int_val : ℚ) - decimal_fraction
        some (round_to_nearest_int full_rat)
      | _, _ => none
    else none
  else none

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  use implementation s
  constructor
  · rfl
  · simp [implementation, problem_spec]
    by_cases h : is_valid_numeric_string s
    · simp [h]
      constructor
      · simp [is_valid_numeric_string] at h
        exact h
      · constructor
        · intro h_len
          simp [String.split] at h_len
          rfl
        · intro h_len
          simp [String.split] at h_len
          apply And.intro
          · simp [round_to_nearest_int, floor_rat]
            simp [abs]
            split_ifs <;> norm_num
          · constructor
            · intro h_neg h_eq
              simp [round_to_nearest_int, floor_rat]
              simp [abs] at h_eq
              norm_num
            · intro h_not_neg h_eq
              simp [round_to_nearest_int, floor_rat]
              simp [abs] at h_eq
              norm_num
    · simp [h]
      exact h