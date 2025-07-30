def problem_spec
-- function signature
(implementation: Nat → Nat -> String)
-- inputs
(x base: Nat) :=
-- spec
let spec (result: String) :=
let result_array := result.toList.map (fun c => c.toNat - '0'.toNat);
let pow_array := (List.range result_array.length).map (fun i => base^(result_array.length - i - 1) * result_array[i]!);
let pow_sum := pow_array.sum;
(0 < base ∧ base ≤ 10) ∧
(∀ i, i < result_array.length →
result_array[i]! < base ∧ 0 ≤ result_array[i]! →
pow_sum = x);
-- program termination
∃ result, implementation x base = result ∧
spec result

-- LLM HELPER
def toBaseString (x base: Nat) : String :=
  if x = 0 then "0"
  else
    let rec helper (n: Nat) : String :=
      if n = 0 then ""
      else
        let digit := n % base
        let rest := n / base
        helper rest ++ (Char.ofNat (digit + '0'.toNat)).toString
    termination_by n
    decreasing_by 
      simp_wf
      have h1 : n ≠ 0 := by simp [*]
      have h2 : 1 < base := by omega
      exact Nat.div_lt_self (Nat.pos_of_ne_zero h1) h2
    helper x

def implementation (x base: Nat) : String := 
  if base > 10 ∨ base ≤ 1 then "0"
  else toBaseString x base

-- LLM HELPER
lemma zero_case_spec (base: Nat) : 
  let result := "0"
  let result_array := result.toList.map (fun c => c.toNat - '0'.toNat)
  let pow_array := (List.range result_array.length).map (fun i => base^(result_array.length - i - 1) * result_array[i]!)
  let pow_sum := pow_array.sum
  (0 < base ∧ base ≤ 10) → 
  (∀ i, i < result_array.length → result_array[i]! < base ∧ 0 ≤ result_array[i]!) ∧ 
  pow_sum = 0 := by
  intro h
  constructor
  · intro i hi
    simp [result, result_array] at hi
    simp [List.length, List.map] at hi
    have : i = 0 := by omega
    simp [this, result_array, List.getElem!]
    constructor
    · simp [Char.toNat]
      omega
    · exact Nat.zero_le _
  · simp [result, result_array, pow_array, pow_sum]
    simp [List.map, List.range, List.sum]
    simp [Char.toNat]
    ring

-- LLM HELPER
lemma valid_base_bounds (base: Nat) : ¬(base > 10 ∨ base ≤ 1) → (0 < base ∧ base ≤ 10) := by
  intro h
  push_neg at h
  omega

theorem correctness
(x base : Nat)
: problem_spec implementation x base := by
  unfold problem_spec implementation
  use (if base > 10 ∨ base ≤ 1 then "0" else toBaseString x base)
  constructor
  · rfl
  · simp
    by_cases h_valid : base > 10 ∨ base ≤ 1
    · simp [h_valid]
      exfalso
      have : ¬(0 < base ∧ base ≤ 10) := by
        push_neg
        cases h_valid with
        | inl h => right; exact h
        | inr h => left; omega
      have spec_req : 0 < base ∧ base ≤ 10 := by
        constructor
        · omega
        · omega
      exact this spec_req
    · simp [h_valid]
      have h_base : 0 < base ∧ base ≤ 10 := valid_base_bounds base h_valid
      constructor
      · exact h_base
      · intro i hi h_digit
        have : x = 0 := by
          by_cases hx : x = 0
          · exact hx
          · simp [toBaseString, hx] at hi
            exfalso
            have : False := by omega
            exact this
        rw [this]
        simp [toBaseString, this]
        apply zero_case_spec
        exact h_base