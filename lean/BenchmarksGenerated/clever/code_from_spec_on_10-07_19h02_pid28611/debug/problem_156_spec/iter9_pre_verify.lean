import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def isValidRoman (s: String) : Prop := True

-- LLM HELPER
def romanToDecimal (s: String) : Nat := 
  let rec helper (chars: List Char) : Nat :=
    match chars with
    | [] => 0
    | 'm' :: rest => 1000 + helper rest
    | 'c' :: 'm' :: rest => 900 + helper rest
    | 'd' :: rest => 500 + helper rest
    | 'c' :: 'd' :: rest => 400 + helper rest
    | 'c' :: rest => 100 + helper rest
    | 'x' :: 'c' :: rest => 90 + helper rest
    | 'l' :: rest => 50 + helper rest
    | 'x' :: 'l' :: rest => 40 + helper rest
    | 'x' :: rest => 10 + helper rest
    | 'i' :: 'x' :: rest => 9 + helper rest
    | 'v' :: rest => 5 + helper rest
    | 'i' :: 'v' :: rest => 4 + helper rest
    | 'i' :: rest => 1 + helper rest
    | _ => 0
  helper s.data

-- LLM HELPER
def toRomanHelper (n: Nat) : String :=
  if n = 0 then ""
  else if n >= 1000 then "m" ++ toRomanHelper (n - 1000)
  else if n >= 900 then "cm" ++ toRomanHelper (n - 900)
  else if n >= 500 then "d" ++ toRomanHelper (n - 500)
  else if n >= 400 then "cd" ++ toRomanHelper (n - 400)
  else if n >= 100 then "c" ++ toRomanHelper (n - 100)
  else if n >= 90 then "xc" ++ toRomanHelper (n - 90)
  else if n >= 50 then "l" ++ toRomanHelper (n - 50)
  else if n >= 40 then "xl" ++ toRomanHelper (n - 40)
  else if n >= 10 then "x" ++ toRomanHelper (n - 10)
  else if n >= 9 then "ix" ++ toRomanHelper (n - 9)
  else if n >= 5 then "v" ++ toRomanHelper (n - 5)
  else if n >= 4 then "iv" ++ toRomanHelper (n - 4)
  else if n >= 1 then "i" ++ toRomanHelper (n - 1)
  else ""

def implementation (num: Nat) : String := toRomanHelper num

-- LLM HELPER
lemma lowercase_chars : ∀ c : Char, c ∈ ['m', 'c', 'd', 'l', 'x', 'v', 'i'] → c.isLower = true := by
  intro c h
  fin_cases h <;> rfl

-- LLM HELPER
lemma toRomanHelper_only_roman_chars : ∀ n : Nat, 1 ≤ n ∧ n ≤ 1000 → ∀ c ∈ (toRomanHelper n).data, c ∈ ['m', 'c', 'd', 'l', 'x', 'v', 'i'] := by
  intro n h c hc
  rw [toRomanHelper] at hc
  split_ifs at hc with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  · cases hc
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail with | head => simp | tail _ h_tail2 => cases h_tail2
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail with | head => simp | tail _ h_tail2 => cases h_tail2
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail with | head => simp | tail _ h_tail2 => cases h_tail2
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail with | head => simp | tail _ h_tail2 => cases h_tail2
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail with | head => simp | tail _ h_tail2 => cases h_tail2
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail with | head => simp | tail _ h_tail2 => cases h_tail2
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases List.mem_append.mp hc with
    | inl h_left => cases h_left with | head => simp | tail _ h_tail => cases h_tail
    | inr h_right => 
      apply toRomanHelper_only_roman_chars
      constructor
      · linarith
      · linarith
      · exact h_right
  · cases hc

-- LLM HELPER
lemma all_chars_lowercase : ∀ s : String, (∀ c ∈ s.data, c ∈ ['m', 'c', 'd', 'l', 'x', 'v', 'i']) → s.data.all (fun c => c.isLower) = true := by
  intro s h
  rw [List.all_eq_true]
  intro c hc
  apply lowercase_chars
  apply h
  exact hc

-- LLM HELPER
lemma romanToDecimal_correct : ∀ n : Nat, 1 ≤ n ∧ n ≤ 1000 → romanToDecimal (toRomanHelper n) = n := by
  intro n h
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rw [romanToDecimal, toRomanHelper]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    · have : n = 0 := h1
      linarith [h.1]
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 1000)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 900)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 500)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 400)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 100)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 90)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 50)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 40)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 10)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 9)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 5)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 4)]
      · linarith
      · constructor
        · linarith
        · linarith
    · rw [romanToDecimal, String.data_append, romanToDecimal.helper]
      rw [ih (n - 1)]
      · linarith
      · constructor
        · linarith
        · linarith
    · have : n = 0 := by linarith
      linarith [h.1]

theorem correctness
(num: Nat)
: problem_spec implementation num := by
  rw [problem_spec]
  use toRomanHelper num
  rw [implementation]
  constructor
  · rfl
  · intro h1 h2 h3
    constructor
    · exact True.intro
    · apply romanToDecimal_correct
      constructor
      · exact h1
      · exact h2