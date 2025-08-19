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
  · simp only [List.length_cons]
    have h_pos : 0 < sizeOf (head :: tail) := by
      rw [List.sizeOf_cons]
      omega
    have h_take_bounded : sizeOf (List.take (List.length tail) (head :: tail)) ≤ sizeOf tail + 1 := by
      induction tail with
      | nil => 
        simp [List.take]
        omega
      | cons head' tail' ih =>
        simp [List.take, List.sizeOf_cons]
        have : List.take (List.length (head' :: tail')) (head :: head' :: tail') = head :: List.take (List.length tail') (head' :: tail') := by
          simp [List.take_cons_succ]
        rw [this, List.sizeOf_cons]
        omega
    rw [List.sizeOf_cons]
    omega

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
    unfold implementation
    rw [if_pos h]
  constructor
  · intro ⟨h_ne, h_mod3⟩
    unfold implementation
    rw [if_neg h_ne]
    simp only [h_mod3, if_true]
  constructor
  · intro ⟨h_ne, h_mod4, h_not_mod3⟩
    unfold implementation
    rw [if_neg h_ne]
    rw [if_neg h_not_mod3]
    rw [if_pos h_mod4]
  · intro ⟨h_ne, h_not_mod3, h_not_mod4⟩
    unfold implementation
    rw [if_neg h_ne]
    rw [if_neg h_not_mod3]
    rw [if_neg h_not_mod4]

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  use implementation lst
  constructor
  · rfl
  · exact implementation_spec_helper lst