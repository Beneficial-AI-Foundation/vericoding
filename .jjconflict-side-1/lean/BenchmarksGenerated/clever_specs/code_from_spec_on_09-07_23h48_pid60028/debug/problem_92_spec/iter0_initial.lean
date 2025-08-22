def problem_spec
(implementation: Rat → Rat → Rat → Bool)
(a: Rat) (b: Rat) (c: Rat) :=
let spec (result : Bool) :=
  let nums := [a, b, c];
  result = true ↔ ∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ (nums[i]! + nums[j]! = nums[k]!) ∧ a.den = 1 ∧ a.den = b.den ∧ a.den = c.den
∃ result,
  implementation a b c = result ∧
  spec result

-- LLM HELPER
def is_integer (r : Rat) : Bool := r.den = 1

-- LLM HELPER
def check_pythagorean_triple (a b c : Rat) : Bool :=
  is_integer a ∧ is_integer b ∧ is_integer c ∧
  (a + b = c ∨ a + c = b ∨ b + c = a)

def implementation (a: Rat) (b: Rat) (c: Rat) : Bool := 
  check_pythagorean_triple a b c

-- LLM HELPER
lemma finite_check_equivalence (a b c : Rat) :
  let nums := [a, b, c]
  (∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ (nums[i]! + nums[j]! = nums[k]!)) ↔
  (a + b = c ∨ a + c = b ∨ b + c = a) := by
  constructor
  · intro h
    obtain ⟨i, j, k, hijk_sub, hij, hjk, hki, hsum⟩ := h
    have h012 : {0, 1, 2} = {0, 1, 2} := rfl
    have hijk : i ∈ {0, 1, 2} ∧ j ∈ {0, 1, 2} ∧ k ∈ {0, 1, 2} := by
      exact ⟨hijk_sub (Set.mem_insert 0 {1, 2}), 
             hijk_sub (Set.mem_insert 1 {2}), 
             hijk_sub (Set.mem_singleton 2)⟩
    interval_cases i <;> interval_cases j <;> interval_cases k
    · contradiction
    · simp [List.getElem_cons_zero, List.getElem_cons_one] at hsum
      exact Or.inr (Or.inl hsum)
    · simp [List.getElem_cons_zero, List.getElem_cons_one] at hsum
      exact Or.inl hsum
    · simp [List.getElem_cons_zero, List.getElem_cons_one] at hsum
      exact Or.inr (Or.inl hsum.symm)
    · contradiction
    · simp [List.getElem_cons_zero, List.getElem_cons_one] at hsum
      exact Or.inr (Or.inr hsum)
    · simp [List.getElem_cons_zero, List.getElem_cons_one] at hsum
      exact Or.inl hsum.symm
    · simp [List.getElem_cons_zero, List.getElem_cons_one] at hsum
      exact Or.inr (Or.inr hsum.symm)
    · contradiction
  · intro h
    cases h with
    | inl h => -- a + b = c
      use 0, 1, 2
      constructor
      · simp [Set.insert_subset_iff]
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · simp [List.getElem_cons_zero, List.getElem_cons_one]
        exact h
    | inr h => 
      cases h with
      | inl h => -- a + c = b
        use 0, 2, 1
        constructor
        · simp [Set.insert_subset_iff]
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · simp [List.getElem_cons_zero, List.getElem_cons_one]
          exact h
      | inr h => -- b + c = a
        use 1, 2, 0
        constructor
        · simp [Set.insert_subset_iff]
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · simp [List.getElem_cons_zero, List.getElem_cons_one]
          exact h

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  use check_pythagorean_triple a b c
  constructor
  · rfl
  · simp [check_pythagorean_triple, is_integer]
    constructor
    · intro h
      constructor
      · rw [finite_check_equivalence]
        exact h.2.2.2
      · exact ⟨h.1, h.2.1, h.2.1⟩
    · intro h
      constructor
      · exact h.2.1
      constructor
      · exact h.2.2.1
      constructor
      · exact h.2.2.2
      · rw [← finite_check_equivalence]
        exact h.1