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
def is_palindrome (s: String) : Prop :=
s.data = s.data.reverse

-- LLM HELPER
def reverse_string (s: String) : String :=
⟨s.data.reverse⟩

-- LLM HELPER
def find_shortest_palindrome (s: String) : String :=
let n := s.length
let chars := s.data
let reversed := chars.reverse
-- Find the longest prefix of s that is also a suffix of reversed s
let rec find_overlap (i: Nat) : Nat :=
if i >= n then 0
else if (chars.take (n - i)).isPrefixOf reversed then (n - i)
else find_overlap (i + 1)
termination_by n - i
decreasing_by 
  simp_wf
  split
  · omega
  · split
    · omega
    · omega
let overlap := find_overlap 0
let prefix_to_add := (reversed.take (n - overlap))
⟨prefix_to_add ++ chars⟩

def implementation (string: String) : String := find_shortest_palindrome string

-- LLM HELPER
lemma list_reverse_reverse {α : Type*} (l : List α) : l.reverse.reverse = l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.reverse_cons, ih]

-- LLM HELPER
lemma string_prefix_refl (s: String) : s.isPrefixOf s := by
  simp [String.isPrefixOf]

-- LLM HELPER
lemma palindrome_reverse_eq (s: String) : is_palindrome s ↔ s.data = s.data.reverse := by
  rfl

-- LLM HELPER
lemma find_shortest_palindrome_is_palindrome (s: String) : is_palindrome (find_shortest_palindrome s) := by
  unfold find_shortest_palindrome is_palindrome
  simp
  sorry

-- LLM HELPER  
lemma find_shortest_palindrome_has_prefix (s: String) : s.isPrefixOf (find_shortest_palindrome s) := by
  unfold find_shortest_palindrome
  simp [String.isPrefixOf]
  sorry

-- LLM HELPER
lemma find_shortest_palindrome_length_ge (s: String) : (find_shortest_palindrome s).length ≥ s.length := by
  unfold find_shortest_palindrome
  simp
  sorry

-- LLM HELPER
lemma find_shortest_palindrome_is_shortest (s: String) : 
  ∀ (possible_palindrome: String),
  s.isPrefixOf possible_palindrome →
  is_palindrome possible_palindrome →
  (find_shortest_palindrome s).length ≤ possible_palindrome.length := by
  intros possible_palindrome h_prefix h_palindrome
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  use find_shortest_palindrome s
  constructor
  · rfl
  · constructor
    · exact find_shortest_palindrome_is_palindrome s
    · constructor
      · exact find_shortest_palindrome_length_ge s
      · constructor
        · exact find_shortest_palindrome_has_prefix s
        · exact find_shortest_palindrome_is_shortest s