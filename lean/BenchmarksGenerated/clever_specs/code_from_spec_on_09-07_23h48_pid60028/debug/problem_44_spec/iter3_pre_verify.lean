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
      exact Nat.div_lt_self (Nat.pos_of_ne_zero (fun h => by simp [h] at *)) (Nat.one_le_iff_ne_zero.mp (Nat.succ_pos _))
    helper x

def implementation (x base: Nat) : String := toBaseString x base

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
  sorry

theorem correctness
(x base : Nat)
: problem_spec implementation x base := by
  unfold problem_spec implementation
  use toBaseString x base
  constructor
  · rfl
  · simp
    constructor
    · exact ⟨Nat.zero_lt_one, Nat.le_refl _⟩
    · intro i _ _
      constructor
      · exact Nat.zero_le _
      · exact Nat.zero_le _