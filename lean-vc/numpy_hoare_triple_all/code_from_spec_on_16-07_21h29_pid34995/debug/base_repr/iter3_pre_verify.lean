import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def digitToChar (digit : Nat) : Char :=
  if digit < 10 then
    Char.ofNat (digit + 48)  -- '0' to '9'
  else
    Char.ofNat (digit + 55)  -- 'A' to 'Z'

-- LLM HELPER
lemma div_lt_self (n base : Nat) (h1 : n > 0) (h2 : base > 1) : n / base < n := by
  have h3 : n / base ≤ n / 2 := by
    apply Nat.div_le_div_left
    exact h2
  have h4 : n / 2 < n := by
    cases' n with n
    · contradiction
    · simp [Nat.div_lt_iff_lt_mul]
      omega
  exact Nat.lt_of_le_of_lt h3 h4

/-- Helper function to convert a natural number to its representation in a given base -/
def natToBaseString (n : Nat) (base : Nat) : String :=
  if n = 0 then "0"
  else
    let rec aux (num : Nat) (acc : List Char) : List Char :=
      if num = 0 then acc
      else aux (num / base) (digitToChar (num % base) :: acc)
    termination_by num
    decreasing_by
      simp_wf
      apply div_lt_self
      · omega
      · omega
    String.mk (aux n [])

/-- Helper function to check if a string represents a valid base-n number -/
def isValidBaseString (s : String) (base : Nat) : Bool :=
  let validChars := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ".take base
  s.length > 0 && s.all (fun c => validChars.contains c)

/-- Helper function to check if a string represents a valid signed base-n number -/
def isValidSignedBaseString (s : String) (base : Nat) : Bool :=
  if s.startsWith "-" then
    isValidBaseString (s.drop 1) base
  else
    isValidBaseString s base

/-- Return a string representation of a number in the given base system.
    
    Converts integers to their representation in bases 2-36. For negative numbers,
    a minus sign is prepended. Supports zero-padding on the left.
-/
def base_repr (number : Int) (base : Nat := 2) (padding : Nat := 0) : Id String :=
  let absNum := number.natAbs
  let baseStr := natToBaseString absNum base
  let paddedStr := 
    if baseStr.length < padding then
      String.mk (List.replicate (padding - baseStr.length) '0') ++ baseStr
    else
      baseStr
  if number < 0 then
    "-" ++ paddedStr
  else
    paddedStr

/-- Specification: base_repr correctly converts integers to base-n strings with proper
    handling of negative numbers and padding -/
theorem base_repr_spec (number : Int) (base : Nat := 2) (padding : Nat := 0) :
    ⦃⌜2 ≤ base ∧ base ≤ 36⌝⦄
    base_repr number base padding
    ⦃⇓result => ⌜
      -- Result is a valid base-n string (possibly with sign)
      isValidSignedBaseString result base = true ∧
      
      -- Length constraints with padding
      (0 ≤ number → max 1 padding ≤ result.length) ∧
      (number < 0 → max 2 (padding + 1) ≤ result.length) ∧
      
      -- Positive numbers: standard base representation with padding
      (0 ≤ number → 
        result = String.mk (List.replicate (padding - (natToBaseString number.natAbs base).length) '0') ++ natToBaseString number.natAbs base) ∧
      
      -- Negative numbers: signed representation with padding
      (number < 0 → 
        result = "-" ++ (String.mk (List.replicate (padding - (natToBaseString number.natAbs base).length) '0') ++ natToBaseString number.natAbs base)) ∧
      
      -- Zero case: special handling
      (number = 0 → 
        result = String.mk (List.replicate (max 1 padding) '0')) ∧
      
      -- No leading zeros in the base representation part (except for padding)
      (¬number = 0 → 
        0 < (if 0 ≤ number then result.drop padding else result.drop (padding + 1)).length ∧
        ¬(if 0 ≤ number then result.drop padding else result.drop (padding + 1)).front = '0')
    ⌝⦄ := by
  simp [base_repr]
  constructor
  · simp [isValidSignedBaseString, isValidBaseString]
    split_ifs with h
    · simp [natToBaseString]
      split_ifs
      · simp
      · simp
    · simp [natToBaseString]
      split_ifs
      · simp
      · simp
  constructor
  · intro h
    simp [natToBaseString]
    split_ifs
    · simp
    · simp
  constructor
  · intro h
    simp [natToBaseString]
    split_ifs
    · simp
    · simp
  constructor
  · intro h
    simp [natToBaseString]
    split_ifs with h1
    · simp at h1
      simp [h1] at h
      rw [Int.natAbs_eq] at h1
      simp [h1]
    · simp
  constructor
  · intro h
    simp [natToBaseString]
    split_ifs with h1
    · simp at h1
      have : number.natAbs = 0 := by
        rw [Int.natAbs_eq]
        simp [Int.natAbs_pos] at h1
        exact h1
      simp [this] at h
      omega
    · simp
  constructor
  · intro h
    simp [h]
    simp [natToBaseString]
    simp [Int.natAbs_zero]
    simp [max_def]
    split_ifs
    · simp
    · simp
  · intro h
    simp [natToBaseString]
    split_ifs with h1
    · simp at h1
      simp [h1] at h
      contradiction
    · simp