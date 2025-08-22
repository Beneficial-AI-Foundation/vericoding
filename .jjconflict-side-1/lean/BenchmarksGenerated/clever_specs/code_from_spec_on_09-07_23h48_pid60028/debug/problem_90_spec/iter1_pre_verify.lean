def problem_spec
-- function signature
(implementation: List Int → Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Option Int) :=
  match result with
  | none => ¬ (∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst.get! i < lst.get! j)
  | some result =>
    let smaller_els := lst.filter (· < result);
    0 < smaller_els.length ∧
    smaller_els.all (λ x => x = smaller_els.get! 0);
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def has_smaller_pair (lst: List Int) : Bool :=
  lst.any (fun x => lst.any (fun y => x < y))

-- LLM HELPER
def find_uniform_smaller (lst: List Int) : Option Int :=
  match lst with
  | [] => none
  | x :: xs =>
    let smaller := lst.filter (· < x)
    if smaller.length > 0 && smaller.all (· = smaller.get! 0) then
      some x
    else
      find_uniform_smaller xs

def implementation (lst: List Int) : Option Int :=
  if has_smaller_pair lst then
    find_uniform_smaller lst
  else
    none

-- LLM HELPER
lemma has_smaller_pair_iff (lst: List Int) :
  has_smaller_pair lst = true ↔ ∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst.get! i < lst.get! j := by
  sorry

-- LLM HELPER
lemma find_uniform_smaller_correct (lst: List Int) :
  match find_uniform_smaller lst with
  | none => ∀ x ∈ lst, let smaller := lst.filter (· < x); smaller.length = 0 ∨ ¬smaller.all (· = smaller.get! 0)
  | some result => 
    let smaller_els := lst.filter (· < result);
    0 < smaller_els.length ∧ smaller_els.all (λ x => x = smaller_els.get! 0) := by
  sorry

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec implementation
  simp only [has_smaller_pair]
  split_ifs with h
  · -- Case: has_smaller_pair lst = true
    use find_uniform_smaller lst
    constructor
    · rfl
    · simp only [spec]
      cases h_case : find_uniform_smaller lst with
      | none => 
        have := find_uniform_smaller_correct lst
        simp [h_case] at this
        sorry
      | some result =>
        have := find_uniform_smaller_correct lst
        simp [h_case] at this
        exact this
  · -- Case: has_smaller_pair lst = false
    use none
    constructor
    · rfl
    · simp only [spec]
      rw [← has_smaller_pair_iff] at h
      simp [h]