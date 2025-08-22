def problem_spec
-- function signature
(implementation: String → Int)
-- inputs
(num: String) :=
-- spec
let spec (result: Int) :=
  let num_val (ch : Char) :=
    if ch.isDigit then
      (ch.toNat - '0'.toNat)
    else if ch.isUpper then
      ((ch.toNat - 'A'.toNat) + 10)
    else 0;
  0 < num.length →
  (
    let char_val := num_val num.toList[0]!;
    (Nat.Prime char_val →
      (1 < num.length → result = char_val + implementation (num.drop 1)) ∧
      (1 = num.length → result = char_val)) ∧
    (¬Nat.Prime char_val →
      (1 < num.length → result = implementation (num.drop 1)) ∧
      (1 = num.length → result = 0))
  )
-- program termination
∃ result, implementation num = result ∧
spec result

-- LLM HELPER
def num_val (ch : Char) : Nat :=
  if ch.isDigit then
    (ch.toNat - '0'.toNat)
  else if ch.isUpper then
    ((ch.toNat - 'A'.toNat) + 10)
  else 0

-- LLM HELPER
def implementation (num: String) : Int :=
  if num.length = 0 then 0
  else
    let char_val := num_val num.toList[0]!
    if Nat.Prime char_val then
      if num.length = 1 then char_val
      else char_val + implementation (num.drop 1)
    else
      if num.length = 1 then 0
      else implementation (num.drop 1)

-- LLM HELPER
lemma string_drop_length (s : String) : s.length > 1 → (s.drop 1).length < s.length := by
  intro h
  simp [String.drop]
  omega

-- LLM HELPER
lemma string_drop_nonempty (s : String) : s.length > 1 → (s.drop 1).length > 0 := by
  intro h
  simp [String.drop]
  omega

-- LLM HELPER
lemma list_head_correct (s : String) : s.length > 0 → s.toList[0]! = s.toList.head! := by
  intro h
  simp [List.getElem!]
  rw [List.head!]
  simp

theorem correctness
(num: String)
: problem_spec implementation num := by
  unfold problem_spec
  simp only [implementation]
  use implementation num
  constructor
  · rfl
  · intro h_len
    simp [num_val]
    split_ifs with h_prime h_len_eq h_len_gt
    · -- Prime case, length = 1
      constructor
      · intro _
        constructor
        · intro h_len_gt
          omega
        · intro h_len_eq_alt
          rfl
      · intro h_not_prime
        contradiction
    · -- Prime case, length > 1
      constructor
      · intro _
        constructor
        · intro _
          rfl
        · intro h_len_eq_alt
          omega
      · intro h_not_prime
        contradiction
    · -- Not prime case, length = 1
      constructor
      · intro h_prime
        contradiction
      · intro _
        constructor
        · intro h_len_gt
          omega
        · intro _
          rfl
    · -- Not prime case, length > 1
      constructor
      · intro h_prime
        contradiction
      · intro _
        constructor
        · intro _
          rfl
        · intro h_len_eq_alt
          omega
    · -- Empty string case
      omega