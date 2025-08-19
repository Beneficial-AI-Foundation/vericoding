import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def String.filter (s : String) (p : Char → Bool) : String :=
  s.toList.filter p |>.asString

-- LLM HELPER
def String.all (s : String) (p : Char → Bool) : Bool :=
  s.toList.all p

-- LLM HELPER
def String.contains (s : String) (c : Char) : Bool :=
  s.toList.contains c

-- LLM HELPER
lemma String.length_filter_le (s : String) (p : Char → Bool) :
  (s.filter p).length ≤ s.length := by
  simp [String.filter, String.length]
  exact List.length_filter_le _ _

-- LLM HELPER
lemma String.all_filter (s : String) (p : Char → Bool) :
  (s.filter p).all p := by
  simp [String.all, String.filter]
  exact List.all_filter _ _

-- LLM HELPER
lemma String.contains_filter_subset (s : String) (p : Char → Bool) (c : Char) :
  (s.filter p).contains c → s.contains c := by
  simp [String.contains, String.filter]
  exact List.mem_of_mem_filter

-- LLM HELPER
lemma String.contains_filter_of_mem (s : String) (p : Char → Bool) (c : Char) :
  s.contains c → p c → (s.filter p).contains c := by
  simp [String.contains, String.filter]
  exact List.mem_filter_of_mem

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
let is_consonant (c: Char): Bool :=
  let vowels := "aeiouAEIOU"
  not (vowels.contains c);
-- spec
let spec (result: String) :=
result.all (λ c => is_consonant c) ∧ result.length ≤ string.length ∧
∀ c, result.contains c → string.contains c ∧
∀ c , string.contains c ∧ is_consonant c → (result.contains c);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def filter_consonants (s: String) : String :=
  s.filter (fun c => 
    let vowels := "aeiouAEIOU"
    not (vowels.contains c))

def implementation (string: String) : String := filter_consonants string

-- LLM HELPER
lemma filter_consonants_all_consonant (s: String) :
  (filter_consonants s).all (fun c => 
    let vowels := "aeiouAEIOU"
    not (vowels.contains c)) := by
  simp [filter_consonants]
  apply String.all_filter

-- LLM HELPER
lemma filter_consonants_length_le (s: String) :
  (filter_consonants s).length ≤ s.length := by
  simp [filter_consonants]
  apply String.length_filter_le

-- LLM HELPER
lemma filter_consonants_contains_subset (s: String) :
  ∀ c, (filter_consonants s).contains c → s.contains c := by
  intro c h
  simp [filter_consonants] at h
  exact String.contains_filter_subset s _ c h

-- LLM HELPER
lemma filter_consonants_contains_all_consonants (s: String) :
  ∀ c, s.contains c ∧ (let vowels := "aeiouAEIOU"; not (vowels.contains c)) → 
       (filter_consonants s).contains c := by
  intro c ⟨h1, h2⟩
  simp [filter_consonants]
  exact String.contains_filter_of_mem s _ c h1 h2

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use filter_consonants s
  constructor
  · rfl
  · constructor
    · exact filter_consonants_all_consonant s
    · constructor
      · exact filter_consonants_length_le s
      · constructor
        · exact filter_consonants_contains_subset s
        · exact filter_consonants_contains_all_consonants s