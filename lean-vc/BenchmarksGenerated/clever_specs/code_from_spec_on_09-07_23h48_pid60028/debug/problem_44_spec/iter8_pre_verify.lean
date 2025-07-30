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
      have h2 : 1 < base := by 
        by_cases h : base = 0
        · exfalso
          simp [h] at *
        · by_cases h' : base = 1
          · exfalso
            simp [h'] at *
          · omega
      exact Nat.div_lt_self (Nat.pos_of_ne_zero h1) h2
    helper x

def implementation (x base: Nat) : String := 
  if base > 10 ∨ base = 0 then "0"
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

theorem correctness
(x base : Nat)
: problem_spec implementation x base := by
  unfold problem_spec implementation
  use (if base > 10 ∨ base = 0 then "0" else toBaseString x base)
  constructor
  · rfl
  · simp
    by_cases h_valid : 0 < base ∧ base ≤ 10
    · simp [h_valid]
      constructor
      · exact h_valid
      · intro i hi h_digit
        by_cases h_x_zero : x = 0
        · simp [h_x_zero, toBaseString]
          have zero_spec := zero_case_spec base h_valid
          exact zero_spec.2
        · simp [h_x_zero, toBaseString]
          have zero_spec := zero_case_spec base h_valid
          exact zero_spec.2
    · simp [h_valid]
      constructor
      · push_neg at h_valid
        constructor
        · by_cases h : base = 0
          · simp [h] at h_valid
            omega
          · have : base > 10 := by omega
            omega
        · by_cases h : base = 0
          · simp [h] at h_valid
            omega
          · have : base > 10 := by omega
            omega
      · intro i hi h_digit
        have zero_spec := zero_case_spec 2 (by omega)
        exact zero_spec.2