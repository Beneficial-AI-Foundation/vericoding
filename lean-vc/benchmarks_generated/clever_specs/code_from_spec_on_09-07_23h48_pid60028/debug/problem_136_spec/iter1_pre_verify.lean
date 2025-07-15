def problem_spec
-- function signature
(impl: List Int → Option Int × Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result: Option Int × Option Int) :=
  let (a, b) := result;
  (match a with
  | none => ¬(∃ i, i ∈ lst ∧ i < 0)
  | some a => a < 0 ∧ a ∈ lst ∧ ∀ i, i ∈ lst ∧ i < 0 → i ≤ a) ∧
  (match b with
  | none => ¬(∃ i, i ∈ lst ∧ 0 < i)
  | some b => 0 < b ∧ b ∈ lst ∧ ∀ i, i ∈ lst ∧ 0 < i → b ≤ i)
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def find_max_negative (lst: List Int) : Option Int :=
  lst.foldl (fun acc x => 
    if x < 0 then
      match acc with
      | none => some x
      | some y => some (max x y)
    else acc
  ) none

-- LLM HELPER
def find_min_positive (lst: List Int) : Option Int :=
  lst.foldl (fun acc x => 
    if x > 0 then
      match acc with
      | none => some x
      | some y => some (min x y)
    else acc
  ) none

def implementation (lst: List Int) : (Option Int × Option Int) := 
  (find_max_negative lst, find_min_positive lst)

-- LLM HELPER
lemma find_max_negative_correct (lst: List Int) :
  match find_max_negative lst with
  | none => ¬(∃ i, i ∈ lst ∧ i < 0)
  | some a => a < 0 ∧ a ∈ lst ∧ ∀ i, i ∈ lst ∧ i < 0 → i ≤ a := by
  sorry

-- LLM HELPER
lemma find_min_positive_correct (lst: List Int) :
  match find_min_positive lst with
  | none => ¬(∃ i, i ∈ lst ∧ 0 < i)
  | some b => 0 < b ∧ b ∈ lst ∧ ∀ i, i ∈ lst ∧ 0 < i → b ≤ i := by
  sorry

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  use (find_max_negative lst, find_min_positive lst)
  constructor
  · rfl
  · constructor
    · exact find_max_negative_correct lst
    · exact find_min_positive_correct lst