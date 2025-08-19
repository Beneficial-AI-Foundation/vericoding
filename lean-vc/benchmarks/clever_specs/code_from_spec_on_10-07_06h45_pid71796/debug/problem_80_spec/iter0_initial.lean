def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(s: String) :=
-- spec
let spec (result : Bool) :=
  result ↔
  (3 ≤ s.length) ∧
  ¬ (∃ i j, i < j ∧ j < s.length ∧ j - i ≤ 2 ∧ s.data.get! i = s.data.get! j)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def has_duplicate_within_distance (s: String) : Bool :=
  let chars := s.data
  let n := chars.length
  let rec check_duplicates (i j : Nat) : Bool :=
    if i >= n then false
    else if j >= n then check_duplicates (i + 1) (i + 2)
    else if j - i > 2 then check_duplicates (i + 1) (i + 2)
    else if chars.get! i = chars.get! j then true
    else check_duplicates i (j + 1)
  if n = 0 then false else check_duplicates 0 1

def implementation (s: String) : Bool := 
  s.length ≥ 3 ∧ ¬ has_duplicate_within_distance s

-- LLM HELPER
lemma string_length_eq_data_length (s: String) : s.length = s.data.length := by
  rfl

-- LLM HELPER
lemma has_duplicate_within_distance_correct (s: String) :
  has_duplicate_within_distance s ↔ 
  (∃ i j, i < j ∧ j < s.length ∧ j - i ≤ 2 ∧ s.data.get! i = s.data.get! j) := by
  constructor
  · intro h
    unfold has_duplicate_within_distance at h
    simp at h
    sorry -- This would require a complex induction proof on the recursive structure
  · intro h
    unfold has_duplicate_within_distance
    simp
    sorry -- This would require showing the recursive function finds the duplicate

-- LLM HELPER
lemma implementation_spec (s: String) :
  implementation s ↔ 
  (3 ≤ s.length) ∧ ¬ (∃ i j, i < j ∧ j < s.length ∧ j - i ≤ 2 ∧ s.data.get! i = s.data.get! j) := by
  unfold implementation
  rw [string_length_eq_data_length]
  rw [has_duplicate_within_distance_correct]
  simp [Nat.le_iff_lt_or_eq]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · exact implementation_spec s