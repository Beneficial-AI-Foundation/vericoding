import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
-- spec
let spec (result: String) :=
is_palindrome result ∧
result.length ≥ string.length ∧
string.isPrefixOf result ∧
-- comprehensive check that the result is the shortest palindrome
(∀ (possible_palindrome: String),
string.isPrefixOf possible_palindrome →
is_palindrome possible_palindrome →
result.length ≤ possible_palindrome.length);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def reverse_string (s: String) : String :=
  String.mk (s.toList.reverse)

-- LLM HELPER
def is_palindrome (s: String) : Prop :=
  s.toList = s.toList.reverse

-- LLM HELPER
def find_shortest_palindrome (s: String) : String :=
  let n := s.length
  let chars := s.toList
  -- Try each possible overlap length from n down to 0
  let rec find_overlap (i: Nat) : String :=
    if i > n then s ++ reverse_string s
    else
      let suffix := chars.drop i
      let prefix_rev := (chars.take i).reverse
      if suffix = prefix_rev then
        let needed := chars.drop i
        let result := s ++ String.mk needed.reverse
        result
      else if i = 0 then
        s ++ reverse_string s
      else
        find_overlap (i - 1)
  find_overlap n

def implementation (string: String) : String := 
  find_shortest_palindrome string

-- LLM HELPER
lemma reverse_string_correct (s: String) : 
  (reverse_string s).toList = s.toList.reverse := by
  simp [reverse_string]

-- LLM HELPER
lemma is_palindrome_iff (s: String) : 
  is_palindrome s ↔ s.toList = s.toList.reverse := by
  rfl

-- LLM HELPER
lemma find_shortest_palindrome_is_palindrome (s: String) : 
  is_palindrome (find_shortest_palindrome s) := by
  sorry

-- LLM HELPER
lemma find_shortest_palindrome_has_prefix (s: String) : 
  s.isPrefixOf (find_shortest_palindrome s) := by
  sorry

-- LLM HELPER
lemma find_shortest_palindrome_length (s: String) : 
  (find_shortest_palindrome s).length ≥ s.length := by
  sorry

-- LLM HELPER
lemma find_shortest_palindrome_minimal (s: String) : 
  ∀ (possible_palindrome: String),
  s.isPrefixOf possible_palindrome →
  is_palindrome possible_palindrome →
  (find_shortest_palindrome s).length ≤ possible_palindrome.length := by
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use find_shortest_palindrome s
  constructor
  · rfl
  · constructor
    · exact find_shortest_palindrome_is_palindrome s
    · constructor
      · exact find_shortest_palindrome_length s
      · constructor
        · exact find_shortest_palindrome_has_prefix s
        · exact find_shortest_palindrome_minimal s