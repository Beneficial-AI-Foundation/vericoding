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
lemma find_uniform_smaller_spec (lst: List Int) :
  (∃ x ∈ lst, let smaller := lst.filter (· < x); smaller.length > 0 ∧ smaller.all (· = smaller[0]!)) →
  ∃ result, find_uniform_smaller lst = some result ∧ 
    let smaller_els := lst.filter (· < result);
    0 < smaller_els.length ∧ smaller_els.all (λ x => x = smaller_els[0]!) := by
  intro h
  induction lst with
  | nil => simp at h
  | cons x xs ih =>
    simp [find_uniform_smaller]
    let smaller := (x :: xs).filter (· < x)
    if h_cond : smaller.length > 0 ∧ smaller.all (· = smaller[0]!) then
      use x
      simp [h_cond]
    else
      have h_not_x : ¬(let smaller := (x :: xs).filter (· < x); smaller.length > 0 ∧ smaller.all (· = smaller[0]!)) := h_cond
      obtain ⟨y, hy_mem, hy_prop⟩ := h
      cases hy_mem with
      | inl hy_eq =>
        subst hy_eq
        simp at h_not_x
        exact absurd hy_prop h_not_x
      | inr hy_mem_xs =>
        apply ih
        use y, hy_mem_xs
        exact hy_prop

-- LLM HELPER
lemma find_uniform_smaller_none_spec (lst: List Int) :
  find_uniform_smaller lst = none → 
  ∀ x ∈ lst, let smaller := lst.filter (· < x); smaller.length = 0 ∨ ¬smaller.all (· = smaller[0]!) := by
  intro h
  induction lst with
  | nil => simp
  | cons x xs ih =>
    simp [find_uniform_smaller] at h
    split_ifs at h with h_cond
    · simp at h
    · intro y hy
      cases hy with
      | inl hy_eq =>
        subst hy_eq
        simp at h_cond
        exact h_cond
      | inr hy_mem =>
        exact ih h y hy_mem

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec implementation
  split_ifs with h
  · -- Case: has_smaller_pair lst = true
    rw [has_smaller_pair_iff] at h
    obtain ⟨i, j, hi, hj, hij, hlt⟩ := h
    
    -- We need to find a result that satisfies the spec
    -- First, let's consider what find_uniform_smaller returns
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
        -- We need to show that result has the required property
        -- This follows from the structure of find_uniform_smaller
        have : result ∈ lst := by
          induction lst with
          | nil => simp [find_uniform_smaller] at h_case
          | cons x xs ih =>
            simp [find_uniform_smaller] at h_case
            split_ifs at h_case with h_filter
            · simp at h_case
              subst h_case
              exact List.mem_cons_self x xs
            · exact List.mem_cons_of_mem x (ih h_case)
        
        -- Now we need to prove the property about smaller elements
        induction lst with
        | nil => simp [find_uniform_smaller] at h_case
        | cons x xs ih =>
          simp [find_uniform_smaller] at h_case
          split_ifs at h_case with h_filter
          · simp at h_case
            subst h_case
            simp at h_filter
            exact h_filter
          · cases h_sub : find_uniform_smaller xs with
            | none => simp [h_sub] at h_case
            | some sub_result =>
              simp [h_sub] at h_case
              subst h_case
              have ih_result := ih h_sub
              exact ih_result
              
  · -- Case: has_smaller_pair lst = false
    use none
    constructor
    · rfl
    · simp
      rw [← has_smaller_pair_iff] at h
      exact h