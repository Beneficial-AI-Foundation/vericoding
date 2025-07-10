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
  if base > 10 ∨ base = 0 then "0"
  else toBaseString x base

-- LLM HELPER
lemma char_toNat_correct (d: Nat) (h: d < 10) : 
  (Char.ofNat (d + '0'.toNat)).toNat - '0'.toNat = d := by
  simp [Char.toNat, Char.ofNat]
  norm_cast

-- LLM HELPER
lemma toBaseString_correct (x base: Nat) (h1: 0 < base) (h2: base ≤ 10) :
  let result := toBaseString x base
  let result_array := result.toList.map (fun c => c.toNat - '0'.toNat)
  let pow_array := (List.range result_array.length).map (fun i => base^(result_array.length - i - 1) * result_array[i]!)
  let pow_sum := pow_array.sum
  (∀ i, i < result_array.length → result_array[i]! < base ∧ 0 ≤ result_array[i]!) ∧ pow_sum = x := by
  constructor
  · intro i hi
    constructor
    · sorry
    · exact Nat.zero_le _
  · sorry

-- LLM HELPER
lemma zero_spec (base: Nat) : 
  let result := "0"
  let result_array := result.toList.map (fun c => c.toNat - '0'.toNat)
  let pow_array := (List.range result_array.length).map (fun i => base^(result_array.length - i - 1) * result_array[i]!)
  let pow_sum := pow_array.sum
  (0 < base ∧ base ≤ 10) → pow_sum = 0 := by
  intro h
  simp [result, result_array, pow_array, pow_sum]
  simp [List.map, List.range, List.sum]
  simp [Char.toNat]
  norm_cast
  ring

theorem correctness
(x base : Nat)
: problem_spec implementation x base := by
  unfold problem_spec implementation
  use implementation x base
  constructor
  · rfl
  · simp
    by_cases h_base_zero : base = 0
    · simp [h_base_zero]
      constructor
      · constructor <;> omega
      · intro i hi h_digit
        simp at h_digit
        omega
    · by_cases h_base_large : base > 10
      · simp [h_base_large]
        constructor
        · constructor <;> omega
        · intro i hi h_digit
          simp at h_digit
          omega
      · simp [h_base_large, h_base_zero]
        constructor
        · constructor
          · omega
          · omega
        · intro i hi h_digit
          by_cases h_x_zero : x = 0
          · simp [h_x_zero, toBaseString]
            have : i = 0 := by
              simp [toBaseString] at hi
              exact Nat.eq_zero_of_lt_one hi
            simp [this]
            constructor
            · simp at h_digit
              omega
            · apply zero_spec
              constructor <;> omega
          · simp [h_x_zero, toBaseString]
            have h_base_pos : 0 < base := by omega
            have h_base_le : base ≤ 10 := by omega
            constructor
            · sorry
            · sorry