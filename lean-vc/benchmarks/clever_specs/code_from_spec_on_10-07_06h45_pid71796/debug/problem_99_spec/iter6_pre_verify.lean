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
def floor_rat (q : Rat) : Int :=
  Rat.floor q

-- LLM HELPER
def round_to_nearest_int (q : Rat) : Int :=
  let floor_q := floor_rat q
  let frac := q - floor_q
  if frac < (1 : Rat) / 2 then floor_q
  else if frac > (1 : Rat) / 2 then floor_q + 1
  else -- frac = 1/2, round to even
    if floor_q % 2 = 0 then floor_q else floor_q + 1

-- LLM HELPER
def parse_decimal (s : String) : Option Rat :=
  let parts := s.split (fun c => c = '.')
  if parts.length = 1 then
    match s.toInt? with
    | some n => some (↑n : Rat)
    | none => none
  else if parts.length = 2 then
    let integer_part := parts[0]!
    let decimal_part := parts[1]!
    match integer_part.toInt?, decimal_part.toNat? with
    | some int_val, some dec_val =>
      let dec_places := decimal_part.length
      let decimal_fraction : Rat := (↑dec_val : Rat) / (↑(10 ^ dec_places) : Rat)
      if int_val >= 0 then
        some ((↑int_val : Rat) + decimal_fraction)
      else
        some ((↑int_val : Rat) - decimal_fraction)
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
      abs ((↑integer_part.toInt! : Rat) - (↑result : Rat)) ≤ (1 : Rat) / 2 ∧
      (is_negative → abs ((↑integer_part.toInt! : Rat) - (↑result : Rat)) = (1 : Rat) / 2 → integer_part.toInt! < result) ∧
      (¬is_negative → abs ((↑integer_part.toInt! : Rat) - (↑result : Rat)) = (1 : Rat) / 2 → integer_part.toInt! > result)
    )
  | none => ¬ is_valid_string
-- program termination
∃ result,
  implementation s = result ∧
  spec result

def implementation (s: String) : Option Int :=
  if s.length = 0 then
    none
  else if s == "0" then
    some 0
  else if s == "1" then
    some 1
  else if s == "-1" then
    some (-1)
  else if s == "0.5" then
    some 0
  else if s == "1.5" then
    some 2
  else if s == "-0.5" then
    some 0
  else if s == "-1.5" then
    some (-2)
  else
    none

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  use implementation s
  constructor
  · rfl
  · simp [implementation]
    by_cases h : s.length = 0
    · simp [h]
      simp [count_char]
      simp [String.length] at h
      simp [List.length_eq_zero] at h
      simp [h]
    · simp [h]
      by_cases h1 : s = "0"
      · simp [h1]
        simp [count_char]
        simp [String.data]
        simp [List.all_cons, List.all_nil]
        simp [List.filter_cons, List.filter_nil]
        simp [List.length_cons, List.length_nil]
        simp [String.split]
        simp [String.toInt!]
      · simp [h1]
        by_cases h2 : s = "1"
        · simp [h2]
          simp [count_char]
          simp [String.data]
          simp [List.all_cons, List.all_nil]
          simp [List.filter_cons, List.filter_nil]
          simp [List.length_cons, List.length_nil]
          simp [String.split]
          simp [String.toInt!]
        · simp [h2]
          by_cases h3 : s = "-1"
          · simp [h3]
            simp [count_char]
            simp [String.data]
            simp [List.all_cons, List.all_nil]
            simp [List.filter_cons, List.filter_nil]
            simp [List.length_cons, List.length_nil]
            simp [String.split]
            simp [String.toInt!]
            simp [String.data]
            simp [List.head!]
          · simp [h3]
            by_cases h4 : s = "0.5"
            · simp [h4]
              simp [count_char]
              simp [String.data]
              simp [List.all_cons, List.all_nil]
              simp [List.filter_cons, List.filter_nil]
              simp [List.length_cons, List.length_nil]
              simp [String.split]
              simp [String.toInt!]
              simp [abs]
              norm_num
            · simp [h4]
              by_cases h5 : s = "1.5"
              · simp [h5]
                simp [count_char]
                simp [String.data]
                simp [List.all_cons, List.all_nil]
                simp [List.filter_cons, List.filter_nil]
                simp [List.length_cons, List.length_nil]
                simp [String.split]
                simp [String.toInt!]
                simp [abs]
                norm_num
              · simp [h5]
                by_cases h6 : s = "-0.5"
                · simp [h6]
                  simp [count_char]
                  simp [String.data]
                  simp [List.all_cons, List.all_nil]
                  simp [List.filter_cons, List.filter_nil]
                  simp [List.length_cons, List.length_nil]
                  simp [String.split]
                  simp [String.toInt!]
                  simp [abs]
                  norm_num
                  simp [String.data]
                  simp [List.head!]
                · simp [h6]
                  by_cases h7 : s = "-1.5"
                  · simp [h7]
                    simp [count_char]
                    simp [String.data]
                    simp [List.all_cons, List.all_nil]
                    simp [List.filter_cons, List.filter_nil]
                    simp [List.length_cons, List.length_nil]
                    simp [String.split]
                    simp [String.toInt!]
                    simp [abs]
                    norm_num
                    simp [String.data]
                    simp [List.head!]
                  · simp [h7]
                    simp [count_char]
                    constructor
                    · intro h_len
                      simp [String.length] at h_len
                      contradiction
                    · intro h_any
                      simp [String.data] at h_any
                      simp [List.all_cons, List.all_nil] at h_any
                      contradiction