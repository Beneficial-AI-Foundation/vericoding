import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Std.HashMap Char Nat)
-- inputs
(s: String) :=
-- spec
let spec (result : Std.HashMap Char Nat) :=
    let chars := s.splitOn " "
    chars.all (fun c => c.length = 1) ∧ s.all (fun c => c.isLower ∨ c = ' ') →
    ∀ key ∈ result.keys,
      (key.isLower ∧
      key ∈ s.data ∧
      result.get! key = s.count key) ∧
    (∀ char ∈ s.data, char.isLower →
      ((∃ char2 ∈ s.data, char2.isLower ∧ char2 ≠ char ∧
      s.count char < s.count char2) ↔ char ∉ result.keys))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def getMostFrequentChars (s: String) : Std.HashMap Char Nat :=
  let lowerChars := s.data.filter (fun c => c.isLower)
  if lowerChars.isEmpty then
    Std.HashMap.empty
  else
    let charCounts := lowerChars.map (fun c => (c, s.count c))
    let maxCount := charCounts.map (fun (_, count) => count) |>.max?
    match maxCount with
    | none => Std.HashMap.empty
    | some max => 
      let mostFrequent := charCounts.filter (fun (_, count) => count = max)
      mostFrequent.foldl (fun acc (char, count) => acc.insert char count) Std.HashMap.empty

def implementation (s: String) : Std.HashMap Char Nat := getMostFrequentChars s

-- LLM HELPER
lemma implementation_correct_aux (s: String) (h_valid: s.all (fun c => c.isLower ∨ c = ' ')) :
  ∀ key ∈ (implementation s).keys,
    (key.isLower ∧
    key ∈ s.data ∧
    (implementation s).get! key = s.count key) ∧
  (∀ char ∈ s.data, char.isLower →
    ((∃ char2 ∈ s.data, char2.isLower ∧ char2 ≠ char ∧
    s.count char < s.count char2) ↔ char ∉ (implementation s).keys)) := by
  simp [implementation, getMostFrequentChars]
  constructor
  · intro key h_key
    constructor
    · constructor
      · simp at h_key
        by_cases h : s.data.filter (fun c => c.isLower) = []
        · simp [h] at h_key
          exact False.elim h_key
        · simp [h] at h_key
          cases' (s.data.filter (fun c => c.isLower)).map (fun c => (c, s.count c)) |>.max? with
          | none => simp at h_key
          | some max => 
            simp [List.foldl] at h_key
            apply Classical.choose_spec
      · simp at h_key
        by_cases h : s.data.filter (fun c => c.isLower) = []
        · simp [h] at h_key
          exact False.elim h_key
        · simp [h] at h_key
          cases' (s.data.filter (fun c => c.isLower)).map (fun c => (c, s.count c)) |>.max? with
          | none => simp at h_key
          | some max => 
            simp [List.foldl] at h_key
            apply Classical.choose_spec
    · simp at h_key
      by_cases h : s.data.filter (fun c => c.isLower) = []
      · simp [h] at h_key
        exact False.elim h_key
      · simp [h] at h_key
        cases' (s.data.filter (fun c => c.isLower)).map (fun c => (c, s.count c)) |>.max? with
        | none => simp at h_key
        | some max => 
          simp [List.foldl] at h_key
          apply Classical.choose_spec
  · intro char h_char h_lower
    constructor
    · intro ⟨char2, h_char2, h_lower2, h_neq, h_count⟩
      simp
      by_cases h : s.data.filter (fun c => c.isLower) = []
      · simp [h]
        rw [List.filter_eq_nil] at h
        have : char ∉ s.data := by
          intro h_in
          have : char.isLower := h_lower
          have : ¬(char.isLower ∨ char = ' ') := h char h_in
          simp [this] at this
        exact this h_char
      · simp [h]
        cases' (s.data.filter (fun c => c.isLower)).map (fun c => (c, s.count c)) |>.max? with
        | none => simp
        | some max => 
          simp [List.foldl]
          apply Classical.choose_spec
    · intro h_not_in_keys
      simp at h_not_in_keys
      by_cases h : s.data.filter (fun c => c.isLower) = []
      · rw [List.filter_eq_nil] at h
        have : char ∉ s.data := by
          intro h_in
          have : char.isLower := h_lower
          have : ¬(char.isLower ∨ char = ' ') := h char h_in
          simp [this] at this
        exact False.elim (this h_char)
      · simp [h] at h_not_in_keys
        cases' (s.data.filter (fun c => c.isLower)).map (fun c => (c, s.count c)) |>.max? with
        | none => simp at h_not_in_keys
        | some max => 
          simp [List.foldl] at h_not_in_keys
          apply Classical.choose_spec

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · intro h
    exact implementation_correct_aux s h.2