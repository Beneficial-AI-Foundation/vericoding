def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Int) :=
lst ≠ [] → ∀ i,  i < lst.length ∧ i % 2 = 0 →
  (lst.length = 1 → impl lst = 0) ∧
  (i + 1 < lst.length →
    (lst[i + 1]! % 2 = 1 →
    impl (lst.drop i) = lst[i + 1]! + (if i + 2 < lst.length then impl (lst.drop (i+2)) else 0)) ∧
    (lst[i + 1]! % 2 = 0 →
    impl (lst.drop i) = if i + 2 < lst.length then impl (lst.drop (i+2)) else 0)
  )
-- program terminates
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def implementation (lst: List Int) : Int :=
  match lst with
  | [] => 0
  | [_] => 0
  | _ :: second :: rest =>
    if second % 2 = 1 then
      second + implementation rest
    else
      implementation rest

-- LLM HELPER
lemma implementation_drop_eq (lst: List Int) (i: Nat) :
  implementation (lst.drop i) = 
  match lst.drop i with
  | [] => 0
  | [_] => 0
  | _ :: second :: rest =>
    if second % 2 = 1 then
      second + implementation rest
    else
      implementation rest := by
  simp [implementation]

-- LLM HELPER
lemma drop_cons_eq (a: Int) (lst: List Int) : 
  (a :: lst).drop 1 = lst := by
  simp [List.drop]

-- LLM HELPER
lemma drop_cons_cons_eq (a b: Int) (lst: List Int) : 
  (a :: b :: lst).drop 2 = lst := by
  simp [List.drop]

-- LLM HELPER
lemma length_drop (lst: List Int) (i: Nat) : 
  i ≤ lst.length → (lst.drop i).length = lst.length - i := by
  intro h
  exact List.length_drop i lst

-- LLM HELPER
lemma get_drop (lst: List Int) (i j: Nat) (h: i + j < lst.length) :
  (lst.drop i)[j]! = lst[i + j]! := by
  simp [List.getElem_drop]

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · intro h_nonempty i h_i
    have h_even := h_i.2
    have h_bound := h_i.1
    constructor
    · intro h_len_one
      simp [implementation]
      cases' lst with hd tl
      · contradiction
      · cases' tl with hd2 tl2
        · rfl
        · simp at h_len_one
    · intro h_succ
      constructor
      · intro h_odd
        rw [implementation_drop_eq]
        cases' ht : lst.drop i with hd tl
        · have : lst.length ≤ i := by
            by_contra h_not
            push_neg at h_not
            have : (lst.drop i).length > 0 := by
              rw [length_drop]
              · omega
              · omega
            rw [ht] at this
            simp at this
          omega
        · cases' tl with hd2 tl2
          · have : lst.length = i + 1 := by
              have : (lst.drop i).length = 1 := by
                rw [ht]
                simp
              rw [length_drop] at this
              · omega
              · omega
            omega
          · simp
            have : hd2 = lst[i + 1]! := by
              rw [← get_drop lst i 1]
              · omega
              · rw [ht]
                simp
            rw [this, h_odd]
            simp
            congr 1
            have : tl2 = lst.drop (i + 2) := by
              rw [← List.drop_drop]
              rw [ht]
              simp [List.drop]
            rw [this]
            split_ifs with h_bound2
            · rfl
            · have : lst.drop (i + 2) = [] := by
                apply List.eq_nil_of_length_eq_zero
                rw [length_drop]
                · omega
                · omega
              rw [this]
              simp [implementation]
      · intro h_even2
        rw [implementation_drop_eq]
        cases' ht : lst.drop i with hd tl
        · have : lst.length ≤ i := by
            by_contra h_not
            push_neg at h_not
            have : (lst.drop i).length > 0 := by
              rw [length_drop]
              · omega
              · omega
            rw [ht] at this
            simp at this
          omega
        · cases' tl with hd2 tl2
          · have : lst.length = i + 1 := by
              have : (lst.drop i).length = 1 := by
                rw [ht]
                simp
              rw [length_drop] at this
              · omega
              · omega
            omega
          · simp
            have : hd2 = lst[i + 1]! := by
              rw [← get_drop lst i 1]
              · omega
              · rw [ht]
                simp
            rw [this, h_even2]
            simp
            have : tl2 = lst.drop (i + 2) := by
              rw [← List.drop_drop]
              rw [ht]
              simp [List.drop]
            rw [this]
            split_ifs with h_bound2
            · rfl
            · have : lst.drop (i + 2) = [] := by
                apply List.eq_nil_of_length_eq_zero
                rw [length_drop]
                · omega
                · omega
              rw [this]
              simp [implementation]