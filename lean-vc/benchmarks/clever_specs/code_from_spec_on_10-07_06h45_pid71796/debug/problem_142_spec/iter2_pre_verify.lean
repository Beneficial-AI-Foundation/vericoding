def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(lst : List Int) :=
-- spec
let spec (result : Int) :=
let last := lst.length-1;
(lst = [] → result = 0) ∧
(lst ≠ [] ∧ last % 3 = 0 → result = lst[last]! ^ 2 + impl (lst.take last)) ∧
(lst ≠ [] ∧ last % 4 = 0 ∧ last % 3 != 0 → result = lst[last]! ^ 3 + impl (lst.take last)) ∧
(lst ≠ [] ∧ last % 3 != 0 ∧ last % 4 != 0 → result = lst[last]! + impl (lst.take last))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
theorem list_take_size_lt (lst : List Int) (h : lst ≠ []) : 
  sizeOf (List.take (lst.length - 1) lst) < sizeOf lst := by
  cases' lst with head tail
  · contradiction
  · simp [List.take, List.sizeOf_cons]
    cases' tail with head' tail'
    · simp [List.sizeOf_cons, List.sizeOf_nil]
      norm_num
    · simp only [List.length_cons, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      rw [List.sizeOf_cons, List.sizeOf_cons]
      simp only [List.take]
      have : sizeOf (List.take (List.length tail') (head' :: tail')) ≤ sizeOf (head' :: tail') := by
        apply List.sizeOf_take_le
      linarith [sizeOf_pos head]

def implementation (lst : List Int) : Int :=
  if lst = [] then 0
  else
    let last := lst.length - 1
    let last_elem := lst[last]!
    let rest := implementation (lst.take last)
    if last % 3 = 0 then
      last_elem ^ 2 + rest
    else if last % 4 = 0 then
      last_elem ^ 3 + rest
    else
      last_elem + rest
termination_by sizeOf lst
decreasing_by
  apply list_take_size_lt
  assumption

-- LLM HELPER
theorem implementation_spec_helper (lst : List Int) : 
  let result := implementation lst
  let last := lst.length - 1
  (lst = [] → result = 0) ∧
  (lst ≠ [] ∧ last % 3 = 0 → result = lst[last]! ^ 2 + implementation (lst.take last)) ∧
  (lst ≠ [] ∧ last % 4 = 0 ∧ last % 3 ≠ 0 → result = lst[last]! ^ 3 + implementation (lst.take last)) ∧
  (lst ≠ [] ∧ last % 3 ≠ 0 ∧ last % 4 ≠ 0 → result = lst[last]! + implementation (lst.take last)) := by
  constructor
  · intro h
    simp [implementation, h]
  constructor
  · intro ⟨h_ne, h_mod3⟩
    simp [implementation, h_ne, h_mod3]
  constructor
  · intro ⟨h_ne, h_mod4, h_not_mod3⟩
    simp [implementation, h_ne, h_not_mod3, h_mod4]
  · intro ⟨h_ne, h_not_mod3, h_not_mod4⟩
    simp [implementation, h_ne, h_not_mod3, h_not_mod4]

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  use implementation lst
  constructor
  · rfl
  · exact implementation_spec_helper lst