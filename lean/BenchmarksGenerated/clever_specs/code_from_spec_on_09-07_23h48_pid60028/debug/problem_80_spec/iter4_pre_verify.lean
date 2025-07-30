def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(s: String) :=
-- spec
let spec (result : Bool) :=
  result ↔
  (3 ≤ s.length) ∧
  ¬ (∃ i j, i < j ∧ j < s.length ∧ j - i ≤ 2 ∧ s.data[i]! = s.data[j]!)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def has_duplicate_within_distance (s: String) : Bool :=
  let chars := s.data
  let n := chars.length
  let rec check (i j : Nat) : Bool :=
    if i >= n then false
    else if j >= n then check (i + 1) (i + 2)
    else if j - i > 2 then check (i + 1) (i + 2)
    else if chars[i]! = chars[j]! then true
    else check i (j + 1)
  check 0 1

def implementation (s: String) : Bool :=
  s.length ≥ 3 && !has_duplicate_within_distance s

-- LLM HELPER
lemma has_duplicate_within_distance_correct (s: String) :
  has_duplicate_within_distance s = true ↔ 
  ∃ i j, i < j ∧ j < s.length ∧ j - i ≤ 2 ∧ s.data[i]! = s.data[j]! := by
  constructor
  · intro h
    -- If has_duplicate_within_distance returns true, then there exist i, j
    use 0, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · by_cases h1 : s.length ≥ 2
      · simp
      · simp at h1
        simp [has_duplicate_within_distance] at h
        cases s.length with
        | zero => simp at h
        | succ n => 
          cases n with
          | zero => simp at h
          | succ m => simp at h1
  · intro ⟨i, j, h1, h2, h3, h4⟩
    -- If such i, j exist, then has_duplicate_within_distance returns true
    simp [has_duplicate_within_distance]
    use i, j
    exact ⟨h1, h2, h3, h4⟩

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use (s.length ≥ 3 && !has_duplicate_within_distance s)
  constructor
  · rfl
  · simp
    constructor
    · intro h
      constructor
      · cases h1 : decide (s.length ≥ 3) with
        | true => 
          simp at h1
          exact h1
        | false =>
          simp [h1] at h
      · cases h2 : has_duplicate_within_distance s with
        | true =>
          simp [h2] at h
        | false =>
          simp [h2] at h
          rw [←has_duplicate_within_distance_correct]
          simp [h2]
    · intro ⟨h1, h2⟩
      simp [decide_eq_true_iff_iff.mpr h1]
      rw [has_duplicate_within_distance_correct] at h2
      cases h3 : has_duplicate_within_distance s with
      | true =>
        rw [has_duplicate_within_distance_correct] at h3
        contradiction
      | false =>
        simp