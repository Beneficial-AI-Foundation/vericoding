def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(nums: List Int) :=
-- spec
let spec (result: Int) :=
match nums with
| [] => result = 0
| head::tail =>
  let first_digit := (toString head.natAbs).toList[0]!.toNat - Char.toNat '0';
  let last_digit := head % 10;
  let valid := head > 10 ∧ Odd first_digit ∧ Odd last_digit
  if valid then result = 1 + impl tail else result = impl tail
-- program termination
∃ result, impl nums = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def isOdd (n : Int) : Bool := n % 2 = 1

-- LLM HELPER
def getFirstDigit (n : Int) : Int :=
  let s := toString n.natAbs
  if s.isEmpty then 0
  else (s.toList[0]!.toNat - Char.toNat '0').toInt

-- LLM HELPER
def getLastDigit (n : Int) : Int := n % 10

-- LLM HELPER
def isValidNumber (n : Int) : Bool :=
  n > 10 ∧ isOdd (getFirstDigit n) ∧ isOdd (getLastDigit n)

def implementation (nums: List Int) : Int :=
  match nums with
  | [] => 0
  | head :: tail =>
    if isValidNumber head then
      1 + implementation tail
    else
      implementation tail

-- LLM HELPER
lemma isOdd_iff_Odd (n : Int) : isOdd n = true ↔ Odd n := by
  simp [isOdd, Odd]
  constructor
  · intro h
    use (n - 1) / 2
    rw [mul_div_cancel']
    · linarith
    · norm_num
  · intro ⟨k, h⟩
    rw [h]
    simp [Int.add_mul_mod_self_left]

-- LLM HELPER
lemma getFirstDigit_eq (n : Int) : 
  getFirstDigit n = (toString n.natAbs).toList[0]!.toNat - Char.toNat '0' := by
  simp [getFirstDigit]
  split_ifs with h
  · simp at h
    have : (toString n.natAbs).toList ≠ [] := by
      simp [String.toList_ne_nil_iff]
      simp [toString_ne_empty_iff]
      simp [Int.natAbs_ne_zero]
    contradiction
  · rfl

-- LLM HELPER
lemma getLastDigit_eq (n : Int) : getLastDigit n = n % 10 := by
  simp [getLastDigit]

-- LLM HELPER
lemma isValidNumber_eq (n : Int) : 
  isValidNumber n = true ↔ 
  n > 10 ∧ Odd (getFirstDigit n) ∧ Odd (getLastDigit n) := by
  simp [isValidNumber]
  rw [Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · intro ⟨h1, h2, h3⟩
    exact ⟨h1, (isOdd_iff_Odd _).mp h2, (isOdd_iff_Odd _).mp h3⟩
  · intro ⟨h1, h2, h3⟩
    exact ⟨h1, (isOdd_iff_Odd _).mpr h2, (isOdd_iff_Odd _).mpr h3⟩

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  induction nums with
  | nil =>
    use 0
    simp [implementation]
  | cons head tail ih =>
    obtain ⟨result_tail, h_eq, h_spec⟩ := ih
    simp [implementation]
    split_ifs with h
    · use 1 + result_tail
      constructor
      · simp [h_eq]
      · simp [problem_spec]
        rw [getFirstDigit_eq, getLastDigit_eq]
        have h_valid : head > 10 ∧ Odd (getFirstDigit head) ∧ Odd (getLastDigit head) := by
          rw [← isValidNumber_eq] at h
          exact h
        simp [h_valid, h_eq]
    · use result_tail
      constructor
      · exact h_eq
      · simp [problem_spec]
        rw [getFirstDigit_eq, getLastDigit_eq]
        have h_not_valid : ¬(head > 10 ∧ Odd (getFirstDigit head) ∧ Odd (getLastDigit head)) := by
          rw [← isValidNumber_eq] at h
          simp at h
          exact h
        simp [h_not_valid, h_eq]