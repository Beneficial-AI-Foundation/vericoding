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

theorem correctness
(num: String)
: problem_spec implementation num := by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · intro h_len
    simp [implementation, num_val]
    by_cases h_prime : Nat.Prime (num_val num.toList[0]!)
    · constructor
      · intro _
        by_cases h_len_cases : num.length = 1
        · constructor
          · intro h_gt
            omega
          · intro _
            simp [h_len_cases]
        · constructor
          · intro h_gt
            simp [h_len_cases]
          · intro h_eq
            omega
      · intro h_not_prime
        contradiction
    · constructor
      · intro h_prime_alt
        contradiction
      · intro _
        by_cases h_len_cases : num.length = 1
        · constructor
          · intro h_gt
            omega
          · intro _
            simp [h_len_cases]
        · constructor
          · intro h_gt
            simp [h_len_cases]
          · intro h_eq
            omega