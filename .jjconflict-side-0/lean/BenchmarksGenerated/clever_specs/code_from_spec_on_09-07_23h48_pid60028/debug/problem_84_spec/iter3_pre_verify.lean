def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(n: Nat) :=
-- spec
let spec (result : String) :=
  0 < n →
  result.all (fun c => c = '0' ∨ c = '1') →
  Nat.ofDigits 2 (result.data.map (fun c => if c = '0' then 0 else 1)).reverse = (Nat.digits 10 n).sum
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def digitSum (n : Nat) : Nat :=
  (Nat.digits 10 n).sum

-- LLM HELPER
def natToBinary (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec aux (m : Nat) : String :=
      if m = 0 then ""
      else aux (m / 2) ++ (if m % 2 = 0 then "0" else "1")
    aux n

def implementation (n: Nat) : String := 
  natToBinary (digitSum n)

-- LLM HELPER
lemma string_all_binary (s : String) : s.all (fun c => c = '0' ∨ c = '1') ↔ 
  ∀ c ∈ s.data, c = '0' ∨ c = '1' := by
  simp [String.all, List.all_eq_true]

-- LLM HELPER
lemma natToBinary_all_binary (n : Nat) : (natToBinary n).all (fun c => c = '0' ∨ c = '1') := by
  simp [natToBinary]
  if h : n = 0 then
    simp [h, string_all_binary]
  else
    simp [h]
    induction n using Nat.strong_induction_on with
    | ind m ih => 
      simp [natToBinary]
      if h : m = 0 then
        simp [h, string_all_binary]
      else
        simp [h]
        apply String.all_append
        constructor
        · by_cases h' : m / 2 = 0
          · simp [h', string_all_binary]
          · apply ih
            · exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)
            · exact h'
        · simp [string_all_binary]
          by_cases h' : m % 2 = 0
          · simp [h']
          · simp [h']

-- LLM HELPER
lemma natToBinary_correct (n : Nat) : 
  Nat.ofDigits 2 ((natToBinary n).data.map (fun c => if c = '0' then 0 else 1)).reverse = n := by
  induction n using Nat.strong_induction_on with
  | ind m ih =>
    simp [natToBinary]
    if h : m = 0 then
      simp [h, Nat.ofDigits]
    else
      simp [h]
      have : m / 2 < m := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)
      rw [String.data_append, List.map_append, List.reverse_append, Nat.ofDigits_append]
      simp [List.map_cons, List.reverse_cons, List.reverse_nil]
      by_cases h' : m % 2 = 0
      · simp [h', Nat.ofDigits]
        rw [←ih (m / 2) this]
        simp [Nat.div_add_mod m 2]
        rw [h']
        simp
      · simp [h']
        have : m % 2 = 1 := by
          cases' Nat.mod_two_eq_zero_or_one m with h₁ h₂
          · contradiction
          · exact h₂
        simp [this, Nat.ofDigits]
        rw [←ih (m / 2) this]
        simp [Nat.div_add_mod m 2]
        rw [this]
        simp

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  use natToBinary (digitSum n)
  constructor
  · rfl
  · intro h₁ h₂
    simp [digitSum]
    exact natToBinary_correct (digitSum n)