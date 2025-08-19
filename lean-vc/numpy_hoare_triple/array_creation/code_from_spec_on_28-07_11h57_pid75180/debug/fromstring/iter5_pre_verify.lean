import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def parseFloat (s : String) : Float :=
  match s.toFloat with
  | f => f

-- LLM HELPER
def vectorFromList {n : Nat} (l : List Float) (h : l.length = n) : Vector Float n :=
  ⟨l.toArray, by simp [List.toArray_length, h]⟩

/-- A new 1-D array initialized from text data in a string -/
def fromstring {n : Nat} (input : String) (sep : String) : Id (Vector Float n) :=
  let tokens := input.splitOn sep
  let parsed := tokens.map (fun token => parseFloat token.trim)
  match h : parsed.length with
  | m =>
    if h_eq : m = n then
      vectorFromList parsed (h_eq ▸ h)
    else
      -- This case shouldn't happen given the preconditions, but we need to handle it
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
      (input = "1 2" → sep = " " → n = 2 → result.get ⟨0, Nat.zero_lt_succ 1⟩ = 1.0 ∧ result.get ⟨1, Nat.lt_of_succ_le (Nat.succ_le_of_lt h_n_pos)⟩ = 2.0) ∧
      (input = "1, 2" → sep = "," → n = 2 → result.get ⟨0, Nat.zero_lt_succ 1⟩ = 1.0 ∧ result.get ⟨1, Nat.lt_of_succ_le (Nat.succ_le_of_lt h_n_pos)⟩ = 2.0)
    ⌝⦄

-- LLM HELPER
def Triple.pure {α : Type*} (x : α) : Triple (Id α) (fun _ => True) (fun _ result => result = x) :=
  Triple.mk (fun _ => x) (fun _ => trivial) (fun _ => rfl)

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
  exact {
    pre := fun _ => ⟨h_n_pos, h_sep_nonempty, h_tokens_count, h_tokens_nonempty⟩,
    run := fun _ => fromstring input sep,
    post := fun _ result => by
      simp [fromstring]
      have tokens := input.splitOn sep
      have parsed := tokens.map (fun token => parseFloat token.trim)
      have h_parsed_len : parsed.length = n := by
        simp [map_length, h_tokens_count]
      constructor
      · intro i
        simp [Float.isFinite]
      constructor
      · intro h_input h_sep h_n
        subst h_input h_sep h_n
        simp [vectorFromList, parseFloat]
        constructor <;> rfl
      · intro h_input h_sep h_n
        subst h_input h_sep h_n
        simp [vectorFromList, parseFloat]
        constructor <;> rfl
  }