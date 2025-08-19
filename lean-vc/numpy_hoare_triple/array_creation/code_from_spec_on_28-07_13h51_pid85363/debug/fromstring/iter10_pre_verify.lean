import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def parseFloat (s : String) : Float :=
  match s.toFloat? with
  | some f => f
  | none => 0.0

-- LLM HELPER
def stringToFloat (s : String) : Float :=
  parseFloat s.trim

def fromstring {n : Nat} (input : String) (sep : String) : Id (Vector Float n) := do
  let tokens := input.splitOn sep
  let floats := tokens.map stringToFloat
  Vector.ofFn (fun i => floats[i.val]!)

-- LLM HELPER
lemma list_get_length {α : Type*} (l : List α) (i : Nat) (h : i < l.length) :
  l[i]! = l.get ⟨i, h⟩ := by
  rfl

-- LLM HELPER  
lemma splitOn_length_eq {s sep : String} {n : Nat} (h : (s.splitOn sep).length = n) :
  n = (s.splitOn sep).length := h.symm

-- LLM HELPER
lemma float_of_string_finite (s : String) : Float.isFinite (stringToFloat s) := by
  simp [stringToFloat, parseFloat]
  split
  · simp [Float.isFinite]
  · simp [Float.isFinite]

-- LLM HELPER
lemma example_parse_space : stringToFloat "1" = 1.0 ∧ stringToFloat "2" = 2.0 := by
  simp [stringToFloat, parseFloat]

-- LLM HELPER
lemma example_parse_comma : stringToFloat " 1" = 1.0 ∧ stringToFloat " 2" = 2.0 := by
  simp [stringToFloat, parseFloat]

-- LLM HELPER
lemma ne_of_pos {n : Nat} (h : n > 0) : n ≠ 0 := Nat.ne_of_gt h

-- LLM HELPER
lemma one_lt_two : (1 : Nat) < 2 := by norm_num

theorem fromstring_spec {n : Nat} (input : String) (sep : String)
    (h_n_pos : n > 0)
    (h_sep_nonempty : sep ≠ "")
    (h_tokens_count : (input.splitOn sep).length = n)
    (h_tokens_nonempty : ∀ token ∈ (input.splitOn sep), token.trim ≠ "")
    (h_tokens_numeric : ∀ token ∈ (input.splitOn sep),
      -- Each token represents a valid numeric string
      ∃ val : Float,
        -- The token, when trimmed of whitespace, represents this float value
        True) :  -- Abstract representation of string-to-float conversion
    ⦃⌜n > 0 ∧ sep ≠ "" ∧
      (input.splitOn sep).length = n ∧
      (∀ token ∈ (input.splitOn sep), token.trim ≠ "") ∧
      (∀ token ∈ (input.splitOn sep), ∃ val : Float, True)⌝⦄
    fromstring input sep
    ⦃⇓result => ⌜
      -- The result vector contains parsed float values from the input string
      (∀ i : Fin n,
        ∃ token : String, ∃ val : Float,
          token = (input.splitOn sep)[i.val]! ∧
          result.get i = val ∧
          -- val is the float representation of the trimmed token
          True) ∧
      -- Mathematical properties of the result
      -- 1. All values are finite (no infinity or NaN from parsing)
      (∀ i : Fin n, Float.isFinite (result.get i)) ∧
      -- 2. The parsing preserves the order of tokens
      (∀ i j : Fin n, i.val < j.val →
        -- The i-th element comes from the i-th token in the input
        ∃ token_i token_j : String,
          token_i = (input.splitOn sep)[i.val]! ∧
          token_j = (input.splitOn sep)[j.val]! ∧
          -- And their relative position in the input is preserved
          True) ∧
      -- 3. Example behavior matching NumPy docs
      -- For input "1 2" with sep " ", result should be [1.0, 2.0]
      -- For input "1, 2" with sep ",", result should be [1.0, 2.0]
      (input = "1 2" ∧ sep = " " ∧ n = 2 →
        result.get ⟨0, Nat.zero_lt_of_ne_zero (ne_of_pos h_n_pos)⟩ = 1.0 ∧ result.get ⟨1, one_lt_two⟩ = 2.0) ∧
      (input = "1, 2" ∧ sep = "," ∧ n = 2 →
        result.get ⟨0, Nat.zero_lt_of_ne_zero (ne_of_pos h_n_pos)⟩ = 1.0 ∧ result.get ⟨1, one_lt_two⟩ = 2.0)
    ⌝⦄ := by
  simp [fromstring]
  constructor
  · exact ⟨h_n_pos, h_sep_nonempty, h_tokens_count, h_tokens_nonempty, h_tokens_numeric⟩
  · constructor
    · intro i
      use (input.splitOn sep)[i.val]!
      use stringToFloat (input.splitOn sep)[i.val]!
      constructor
      · rfl
      constructor
      · simp [Vector.get, Vector.ofFn]
      · trivial
    constructor
    · intro i
      simp [Vector.get, Vector.ofFn]
      apply float_of_string_finite
    constructor
    · intro i j h_lt
      use (input.splitOn sep)[i.val]!
      use (input.splitOn sep)[j.val]!
      constructor
      · rfl
      constructor
      · rfl
      · trivial
    constructor
    · intro ⟨h_input, h_sep, h_n⟩
      simp [Vector.get, Vector.ofFn, h_input, h_sep]
      have : (input.splitOn sep) = ["1", "2"] := by simp [h_input, h_sep]
      simp [this, stringToFloat, parseFloat]
    · intro ⟨h_input, h_sep, h_n⟩
      simp [Vector.get, Vector.ofFn, h_input, h_sep]
      have : (input.splitOn sep) = ["1", " 2"] := by simp [h_input, h_sep]
      simp [this, stringToFloat, parseFloat]