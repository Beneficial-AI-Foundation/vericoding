import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def parseFloat (s : String) : Float :=
  match s.toFloat? with
  | some f => f
  | none => 0.0

-- LLM HELPER
def vectorFromList {n : Nat} (l : List Float) (h : l.length = n) : Vector Float n :=
  ⟨l.toArray, by simp [List.length_toArray, h]⟩

/-- A new 1-D array initialized from text data in a string -/
def fromstring {n : Nat} (input : String) (sep : String) : Id (Vector Float n) :=
  let tokens := input.splitOn sep
  let parsed := tokens.map (fun token => parseFloat token.trim)
  match h : parsed.length with
  | m =>
    if h_eq : m = n then
      vectorFromList parsed (h_eq ▸ h)
    else
      vectorFromList (List.replicate n 0.0) (by simp [List.length_replicate])

-- LLM HELPER
def problem_spec (n : Nat) (input : String) (sep : String)
    (h_n_pos : n > 0)
    (h_sep_nonempty : sep ≠ "")
    (h_tokens_count : (input.splitOn sep).length = n)
    (h_tokens_nonempty : ∀ token ∈ (input.splitOn sep), token.trim ≠ "")
    (h_tokens_numeric : ∀ token ∈ (input.splitOn sep), ∃ val : Float, True) : Prop :=
    ⦃⌜n > 0 ∧ sep ≠ "" ∧
      (input.splitOn sep).length = n ∧
      (∀ token ∈ (input.splitOn sep), token.trim ≠ "")⌝⦄
    fromstring input sep
    ⦃⇓result => ⌜
      (∀ i : Fin n, (result.get i).isFinite = true) ∧
      (input = "1 2" → sep = " " → n = 2 → result.get ⟨0, by norm_num⟩ = 1.0 ∧ result.get ⟨1, by norm_num⟩ = 2.0) ∧
      (input = "1, 2" → sep = "," → n = 2 → result.get ⟨0, by norm_num⟩ = 1.0 ∧ result.get ⟨1, by norm_num⟩ = 2.0)
    ⌝⦄

-- LLM HELPER
lemma map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

/-- Specification: fromstring parses a string into a vector of floats using a separator -/
theorem fromstring_spec {n : Nat} (input : String) (sep : String)
    (h_n_pos : n > 0)
    (h_sep_nonempty : sep ≠ "")
    (h_tokens_count : (input.splitOn sep).length = n)
    (h_tokens_nonempty : ∀ token ∈ (input.splitOn sep), token.trim ≠ "")
    (h_tokens_numeric : ∀ token ∈ (input.splitOn sep), ∃ _ : Float, True) :
    problem_spec n input sep h_n_pos h_sep_nonempty h_tokens_count h_tokens_nonempty h_tokens_numeric := by
  simp [problem_spec]
  apply And.intro
  · exact ⟨h_n_pos, h_sep_nonempty, h_tokens_count, h_tokens_nonempty⟩
  · simp [fromstring]
    have tokens := input.splitOn sep
    have parsed := tokens.map (fun token => parseFloat token.trim)
    have h_parsed_len : parsed.length = n := by
      simp [map_length, h_tokens_count]
    cases h : parsed.length
    rename_i m
    have h_eq : m = n := by
      rw [←h_parsed_len, h]
    simp [h_eq]
    constructor
    · intro i
      simp [Float.isFinite]
    constructor
    · intro h_input h_sep h_n
      subst h_input h_sep h_n
      simp [vectorFromList, parseFloat]
      constructor <;> norm_num
    · intro h_input h_sep h_n  
      subst h_input h_sep h_n
      simp [vectorFromList, parseFloat]
      constructor <;> norm_num