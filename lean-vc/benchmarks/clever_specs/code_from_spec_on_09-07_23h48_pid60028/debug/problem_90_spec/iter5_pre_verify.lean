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
lemma find_uniform_smaller_correct (lst: List Int) :
  match find_uniform_smaller lst with
  | none => ∀ x ∈ lst, let smaller := lst.filter (· < x); smaller.length = 0 ∨ ¬smaller.all (· = smaller[0]!)
  | some result => 
    let smaller_els := lst.filter (· < result);
    0 < smaller_els.length ∧ smaller_els.all (λ x => x = smaller_els[0]!) := by
  induction lst with
  | nil => simp [find_uniform_smaller]
  | cons x xs ih =>
    simp [find_uniform_smaller]
    split_ifs with h
    · simp
      constructor
      · simp at h
        exact h.1
      · simp at h
        exact h.2
    · simp at h
      cases h_case : find_uniform_smaller xs with
      | none =>
        simp [h_case]
        intro y hy
        cases hy with
        | inl hy_eq =>
          subst hy_eq
          left
          simp [List.filter_nil_of_false]
          intro z hz
          push_neg at h
          cases h with
          | inl h => exact Nat.not_lt_zero _ h
          | inr h => exact absurd rfl h
        | inr hy_mem =>
          exact ih y hy_mem
      | some result =>
        simp [h_case]
        have := find_uniform_smaller_correct xs
        rw [h_case] at this
        exact this

-- LLM HELPER  
lemma no_smaller_pair_implies_no_uniform_smaller (lst: List Int) :
  has_smaller_pair lst = false → find_uniform_smaller lst = none := by
  intro h
  induction lst with
  | nil => simp [find_uniform_smaller]
  | cons x xs ih =>
    simp [find_uniform_smaller]
    split_ifs with h_filter
    · simp [has_smaller_pair, List.any_eq_true] at h
      push_neg at h
      simp at h_filter
      have ⟨y, hy_mem, hyx⟩ := h_filter.1
      have := h y hy_mem x (List.mem_cons_self x xs)
      exact absurd hyx this
    · apply ih
      simp [has_smaller_pair, List.any_eq_true] at h ⊢
      push_neg at h ⊢
      intro y hy z hz
      exact h y (List.mem_cons_of_mem x hy) z (List.mem_cons_of_mem x hz)

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec implementation
  split_ifs with h
  · -- Case: has_smaller_pair lst = true
    use find_uniform_smaller lst
    constructor
    · rfl
    · cases h_case : find_uniform_smaller lst with
      | none => 
        have := find_uniform_smaller_correct lst
        rw [h_case] at this
        rw [has_smaller_pair_iff] at h
        exfalso
        obtain ⟨i, j, hi, hj, hij, hlt⟩ := h
        have x_mem : lst[i]! ∈ lst := List.getElem_mem _ _ hi
        have := this lst[i]! x_mem
        cases this with
        | inl hempty =>
          simp [List.length_eq_zero, List.filter_eq_nil] at hempty
          have : lst[j]! ∈ lst.filter (· < lst[i]!) := by
            simp [List.mem_filter]
            exact ⟨List.getElem_mem _ _ hj, hlt⟩
          rw [hempty] at this
          exact List.not_mem_nil _ this
        | inr hnot_all =>
          simp [List.all_eq_true, List.all_eq_false] at hnot_all
          obtain ⟨z, hz_mem, hz_ne⟩ := hnot_all
          simp [List.mem_filter] at hz_mem
          have : lst[j]! ∈ lst.filter (· < lst[i]!) := by
            simp [List.mem_filter]
            exact ⟨List.getElem_mem _ _ hj, hlt⟩
          have : lst.filter (· < lst[i]!) ≠ [] := by
            intro contra
            rw [contra] at this
            exact List.not_mem_nil _ this
          cases List.length_pos_iff_ne_nil.mpr this with
          | intro h_pos =>
            have : (lst.filter (· < lst[i]!))[0]! ∈ lst.filter (· < lst[i]!) := List.getElem_mem _ _ h_pos
            exact hz_ne this
      | some result =>
        have := find_uniform_smaller_correct lst
        rw [h_case] at this
        exact this
  · -- Case: has_smaller_pair lst = false
    use none
    constructor
    · rfl
    · simp only
      rw [← has_smaller_pair_iff] at h
      exact h