def problem_spec
-- function signature
(implementation: List Int → Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Option Int) :=
  match result with
  | none => ¬ (∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst[i]! < lst[j]!)
  | some result =>
    let smaller_els := lst.filter (· < result);
    0 < smaller_els.length ∧
    smaller_els.all (λ x => x = smaller_els[0]!);
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
    if smaller.length > 0 && smaller.all (· = smaller[0]!) then
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
  has_smaller_pair lst = true ↔ ∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst[i]! < lst[j]! := by
  unfold has_smaller_pair
  simp [List.any_eq_true]
  constructor
  · intro ⟨x, hx_mem, y, hy_mem, hxy⟩
    obtain ⟨i, hi_bound, hx_eq⟩ := List.mem_iff_get.mp hx_mem
    obtain ⟨j, hj_bound, hy_eq⟩ := List.mem_iff_get.mp hy_mem
    use i, j
    constructor
    · exact hi_bound
    constructor
    · exact hj_bound
    constructor
    · intro hij
      subst hij
      rw [← hx_eq, ← hy_eq] at hxy
      exact lt_irrefl _ hxy
    · rw [← hx_eq, ← hy_eq, List.get_eq_getElem]
      exact hxy
  · intro ⟨i, j, hi, hj, hij, hlt⟩
    use lst[i]!, List.getElem_mem _ _ hi
    use lst[j]!, List.getElem_mem _ _ hj
    exact hlt

-- LLM HELPER
lemma find_uniform_smaller_mem (lst: List Int) (result: Int) :
  find_uniform_smaller lst = some result → result ∈ lst := by
  induction lst with
  | nil => simp [find_uniform_smaller]
  | cons x xs ih =>
    simp [find_uniform_smaller]
    split_ifs with h_filter
    · intro h_eq
      simp at h_eq
      subst h_eq
      exact List.mem_cons_self x xs
    · intro h_eq
      exact List.mem_cons_of_mem x (ih h_eq)

-- LLM HELPER
lemma find_uniform_smaller_prop (lst: List Int) (result: Int) :
  find_uniform_smaller lst = some result → 
  let smaller_els := lst.filter (· < result);
  0 < smaller_els.length ∧ smaller_els.all (λ x => x = smaller_els[0]!) := by
  induction lst with
  | nil => simp [find_uniform_smaller]
  | cons x xs ih =>
    simp [find_uniform_smaller]
    split_ifs with h_filter
    · intro h_eq
      simp at h_eq
      subst h_eq
      simp at h_filter
      exact h_filter
    · intro h_eq
      exact ih h_eq

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec implementation
  split_ifs with h
  · -- Case: has_smaller_pair lst = true
    cases h_case : find_uniform_smaller lst with
    | none => 
      use none
      constructor
      · rfl
      · simp
        rw [← has_smaller_pair_iff]
        exact h
    | some result =>
      use some result
      constructor
      · rfl
      · simp
        exact find_uniform_smaller_prop lst result h_case
              
  · -- Case: has_smaller_pair lst = false
    use none
    constructor
    · rfl
    · simp
      rw [← has_smaller_pair_iff] at h
      exact h