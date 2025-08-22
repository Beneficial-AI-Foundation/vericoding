def problem_spec
-- function signature
(impl: Nat → String)
-- inputs
(num: Nat) :=
-- spec
let spec (result: String) :=
1 ≤ num ∧ num ≤ 1000 ∧ (result.data.all (fun c => c.isLower)) →
isValidRoman result ∧ romanToDecimal result = num
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def isValidRoman (s: String) : Bool := 
  let chars := s.data
  chars.all (fun c => c = 'i' ∨ c = 'v' ∨ c = 'x' ∨ c = 'l' ∨ c = 'c' ∨ c = 'd' ∨ c = 'm')

-- LLM HELPER
def romanToDecimal (s: String) : Nat :=
  let rec helper (chars: List Char) (acc: Nat) : Nat :=
    match chars with
    | [] => acc
    | c :: rest =>
      let val := match c with
        | 'i' => 1
        | 'v' => 5
        | 'x' => 10
        | 'l' => 50
        | 'c' => 100
        | 'd' => 500
        | 'm' => 1000
        | _ => 0
      match rest with
      | [] => acc + val
      | next :: _ =>
        let nextVal := match next with
          | 'i' => 1
          | 'v' => 5
          | 'x' => 10
          | 'l' => 50
          | 'c' => 100
          | 'd' => 500
          | 'm' => 1000
          | _ => 0
        if val < nextVal then
          helper rest (acc - val)
        else
          helper rest (acc + val)
  helper s.data 0

-- LLM HELPER
def decimalToRoman (n: Nat) : String :=
  let pairs := [(1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), 
                (90, "xc"), (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), 
                (5, "v"), (4, "iv"), (1, "i")]
  let rec helper (num: Nat) (ps: List (Nat × String)) (acc: String) : String :=
    match ps with
    | [] => acc
    | (val, rom) :: rest =>
      if num >= val then
        helper (num - val) ps (acc ++ rom)
      else
        helper num rest acc
  termination_by (num, ps.length)
  decreasing_by
    simp_wf
    split_ifs with h
    · constructor
      · exact Nat.sub_lt (Nat.le_of_ble_eq_true h) (by
          simp [val]
          split_ifs <;> norm_num)
      · simp
    · constructor
      · simp
      · simp [List.length]
  helper n pairs ""

def implementation (num: Nat) : String := decimalToRoman num

-- LLM HELPER
lemma all_chars_lowercase (n: Nat) : (decimalToRoman n).data.all (fun c => c.isLower) = true := by
  simp [decimalToRoman]
  have : ∀ s : String, (s = "m" ∨ s = "cm" ∨ s = "d" ∨ s = "cd" ∨ s = "c" ∨ s = "xc" ∨ s = "l" ∨ s = "xl" ∨ s = "x" ∨ s = "ix" ∨ s = "v" ∨ s = "iv" ∨ s = "i") → s.data.all (fun c => c.isLower) = true := by
    intro s h
    cases h with
    | inl h => simp [h]
    | inr h => cases h with
      | inl h => simp [h]
      | inr h => cases h with
        | inl h => simp [h]
        | inr h => cases h with
          | inl h => simp [h]
          | inr h => cases h with
            | inl h => simp [h]
            | inr h => cases h with
              | inl h => simp [h]
              | inr h => cases h with
                | inl h => simp [h]
                | inr h => cases h with
                  | inl h => simp [h]
                  | inr h => cases h with
                    | inl h => simp [h]
                    | inr h => cases h with
                      | inl h => simp [h]
                      | inr h => cases h with
                        | inl h => simp [h]
                        | inr h => cases h with
                          | inl h => simp [h]
                          | inr h => simp [h]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    simp [decimalToRoman]
    split_ifs <;> simp [List.all_append, this]
    all_goals (try apply ih; omega)

-- LLM HELPER
lemma valid_roman_conversion (n: Nat) : n ≥ 1 ∧ n ≤ 1000 → 
  isValidRoman (decimalToRoman n) = true ∧ romanToDecimal (decimalToRoman n) = n := by
  intro h
  constructor
  · simp [isValidRoman, decimalToRoman]
    induction n using Nat.strong_induction_on with
    | h n ih =>
      simp [isValidRoman, decimalToRoman]
      split_ifs <;> simp [List.all_append] <;> try (apply ih; omega)
      all_goals (simp [List.all_cons])
  · simp [romanToDecimal, decimalToRoman]
    induction n using Nat.strong_induction_on with
    | h n ih =>
      simp [romanToDecimal, decimalToRoman]
      split_ifs <;> try (apply ih; omega)
      all_goals simp

theorem correctness
(num: Nat)
: problem_spec implementation num := by
  unfold problem_spec implementation
  use decimalToRoman num
  constructor
  · rfl
  · intro h
    have h1 : 1 ≤ num := h.1
    have h2 : num ≤ 1000 := h.2.1
    have h3 : (decimalToRoman num).data.all (fun c => c.isLower) = true := all_chars_lowercase num
    rw [h3] at h
    have conversion := valid_roman_conversion num ⟨h1, h2⟩
    exact conversion