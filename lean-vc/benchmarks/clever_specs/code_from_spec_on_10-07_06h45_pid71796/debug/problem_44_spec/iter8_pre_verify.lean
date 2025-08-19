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
if base = 0 then "0"
else if x = 0 then "0"
else
  let rec aux (n: Nat) (acc: String) : String :=
    if n = 0 then acc
    else aux (n / base) ((Char.ofNat ('0'.toNat + n % base)).toString ++ acc)
  termination_by n
  decreasing_by 
    simp_wf
    apply Nat.div_lt_self
    · assumption
    · exact Nat.pos_of_ne_zero (fun h => by
        simp at h
        contradiction)
  aux x ""

def implementation (x base: Nat) : String := toBaseString x base

-- LLM HELPER
lemma char_digit_toNat (d: Nat) (h: d < 10) : 
  (Char.ofNat ('0'.toNat + d)).toNat - '0'.toNat = d := by
  simp [Char.toNat, Char.ofNat]
  rw [Nat.add_sub_cancel]

-- LLM HELPER  
lemma base_conversion_correct (x base: Nat) (h_base: 0 < base ∧ base ≤ 10) (hx: x > 0) :
  let result := toBaseString x base
  let result_array := result.toList.map (fun c => c.toNat - '0'.toNat)
  let pow_array := (List.range result_array.length).map (fun i => base^(result_array.length - i - 1) * result_array[i]!)
  let pow_sum := pow_array.sum
  (∀ i, i < result_array.length → result_array[i]! < base ∧ 0 ≤ result_array[i]!) ∧ pow_sum = x := by
  simp [toBaseString, hx, h_base.1]
  constructor
  · intro i hi
    constructor
    · simp
    · simp
  · simp

theorem correctness
(x base : Nat)
: problem_spec implementation x base
:= by
  simp [problem_spec, implementation]
  use toBaseString x base
  constructor
  · rfl
  · simp
    cases' Nat.eq_zero_or_pos base with hb hb
    · simp [toBaseString]
      constructor
      · simp
      · intro i hi
        simp at hi
    · cases' Nat.lt_or_ge base 11 with hb_upper hb_upper
      · have h_base : 0 < base ∧ base ≤ 10 := ⟨hb, Nat.lt_succ_iff.mp hb_upper⟩
        constructor
        · exact h_base
        · intro i hi h_bounds
          cases' Nat.eq_zero_or_pos x with hx hx
          · simp [toBaseString, hx]
          · exact (base_conversion_correct x base h_base hx).2
      · simp [toBaseString]
        constructor
        · constructor
          · exact hb
          · omega
        · intro i hi
          simp at hi