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
  infer_instance

-- LLM HELPER
def num_val (ch : Char) : Nat :=
  if ch.isDigit then
    (ch.toNat - '0'.toNat)
  else if ch.isUpper then
    ((ch.toNat - 'A'.toNat) + 10)
  else 0

-- LLM HELPER
lemma string_drop_shorter (s : String) (h : s.length > 1) : (s.drop 1).length < s.length := by
  rw [String.length_drop]
  omega

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
decreasing_by
  · simp_wf
    apply string_drop_shorter
    omega
  · simp_wf
    apply string_drop_shorter
    omega

theorem correctness
(num: String)
: problem_spec implementation num := by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · intro h_len
    simp only [implementation]
    have h_ne_zero : num.length ≠ 0 := Nat.ne_of_gt h_len
    simp only [if_neg h_ne_zero]
    by_cases h_prime : Nat.Prime (num_val num.toList[0]!)
    · constructor
      · intro _
        constructor
        · intro h_gt
          simp only [if_pos h_prime]
          have h_ne_one : num.length ≠ 1 := Nat.ne_of_gt h_gt
          simp only [if_neg h_ne_one]
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
          have h_ne_one : num.length ≠ 1 := Nat.ne_of_gt h_gt
          simp only [if_neg h_ne_one]
          rfl
        · intro h_eq
          simp only [if_neg h_prime, if_pos h_eq]
          rfl