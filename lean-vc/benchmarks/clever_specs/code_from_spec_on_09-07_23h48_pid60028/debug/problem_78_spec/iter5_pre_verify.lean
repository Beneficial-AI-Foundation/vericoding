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
def Nat.Prime (n : Nat) : Prop :=
  n > 1 ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

-- LLM HELPER
instance (n : Nat) : Decidable (Nat.Prime n) := by
  unfold Nat.Prime
  apply And.decidable

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
termination_by num.length

theorem correctness
(num: String)
: problem_spec implementation num := by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · intro h_len
    unfold implementation
    simp only [num_val]
    by_cases h_prime : Nat.Prime (num_val num.toList[0]!)
    · constructor
      · intro _
        constructor
        · intro h_gt
          simp only [if_pos h_prime]
          by_cases h_len_one : num.length = 1
          · simp only [if_pos h_len_one]
            have : ¬(1 < 1) := Nat.lt_irrefl 1
            exact False.elim (this h_gt)
          · simp only [if_neg h_len_one]
            rfl
        · intro h_eq
          simp only [if_pos h_prime, if_pos h_eq]
          rfl
      · intro h_not_prime
        contradiction
    · constructor
      · intro h_prime_alt
        contradiction
      · intro _
        constructor
        · intro h_gt
          simp only [if_neg h_prime]
          by_cases h_len_one : num.length = 1
          · simp only [if_pos h_len_one]
            have : ¬(1 < 1) := Nat.lt_irrefl 1
            exact False.elim (this h_gt)
          · simp only [if_neg h_len_one]
            rfl
        · intro h_eq
          simp only [if_neg h_prime, if_pos h_eq]
          rfl