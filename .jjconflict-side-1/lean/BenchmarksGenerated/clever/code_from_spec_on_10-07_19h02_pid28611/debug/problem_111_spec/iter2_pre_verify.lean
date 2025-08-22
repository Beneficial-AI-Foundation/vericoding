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
  let charCounts := lowerChars.map (fun c => (c, s.count c))
  let maxCount := charCounts.map (fun (_, count) => count) |>.max?
  match maxCount with
  | none => Std.HashMap.empty
  | some max => 
    let mostFrequent := charCounts.filter (fun (_, count) => count = max)
    mostFrequent.foldl (fun acc (char, count) => acc.insert char count) Std.HashMap.empty

def implementation (s: String) : Std.HashMap Char Nat := getMostFrequentChars s

-- LLM HELPER
lemma empty_string_correctness : problem_spec implementation "" := by
  use Std.HashMap.empty
  simp [implementation, getMostFrequentChars]
  intro h
  simp [Std.HashMap.keys]
  constructor
  · intro key h_key
    simp [Std.HashMap.keys] at h_key
  · intro char h_char
    simp [String.data] at h_char

-- LLM HELPER
lemma single_char_correctness (c: Char) (h_lower: c.isLower) : 
  problem_spec implementation (String.mk [c]) := by
  use (Std.HashMap.empty.insert c 1)
  simp [implementation, getMostFrequentChars]
  sorry

-- LLM HELPER
lemma implementation_satisfies_spec (s: String) : 
  ∃ result, implementation s = result ∧ 
  (let chars := s.splitOn " "
   chars.all (fun c => c.length = 1) ∧ s.all (fun c => c.isLower ∨ c = ' ') →
   ∀ key ∈ result.keys,
     (key.isLower ∧
     key ∈ s.data ∧
     result.get! key = s.count key) ∧
   (∀ char ∈ s.data, char.isLower →
     ((∃ char2 ∈ s.data, char2.isLower ∧ char2 ≠ char ∧
     s.count char < s.count char2) ↔ char ∉ result.keys))) := by
  use implementation s
  constructor
  · rfl
  · intro h
    simp [implementation, getMostFrequentChars]
    sorry

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · intro h
    simp [implementation, getMostFrequentChars]
    constructor
    · intro key h_key
      simp [Std.HashMap.keys] at h_key
      constructor
      · sorry
      · constructor
        · sorry
        · sorry
    · intro char h_char h_lower
      constructor
      · intro ⟨char2, h_char2, h_lower2, h_neq, h_count⟩
        simp [Std.HashMap.keys]
        sorry
      · intro h_not_in_keys
        simp [Std.HashMap.keys] at h_not_in_keys
        sorry