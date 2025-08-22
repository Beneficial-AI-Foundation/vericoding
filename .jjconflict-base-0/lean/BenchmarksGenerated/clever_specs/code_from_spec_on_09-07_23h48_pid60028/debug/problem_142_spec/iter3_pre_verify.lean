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
lemma take_length_lt (lst : List Int) (h : lst ≠ []) : 
  (lst.take (lst.length - 1)).length < lst.length := by
  cases lst with
  | nil => contradiction
  | cons head tail => 
    simp [List.take, List.length]
    cases tail with
    | nil => simp
    | cons _ _ => 
      simp [List.length]
      omega

def implementation (lst : List Int) : Int := 
  match lst with
  | [] => 0
  | _ => 
    let last := lst.length - 1
    let lastElem := lst[last]!
    let rest := implementation (lst.take last)
    if last % 3 = 0 then
      lastElem ^ 2 + rest
    else if last % 4 = 0 then
      lastElem ^ 3 + rest
    else
      lastElem + rest
termination_by lst.length

-- LLM HELPER
lemma implementation_empty : implementation [] = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_nonempty (lst : List Int) (h : lst ≠ []) : 
  let last := lst.length - 1
  let lastElem := lst[last]!
  let rest := implementation (lst.take last)
  implementation lst = 
    if last % 3 = 0 then
      lastElem ^ 2 + rest
    else if last % 4 = 0 then
      lastElem ^ 3 + rest
    else
      lastElem + rest := by
  simp [implementation]
  cases lst with
  | nil => contradiction
  | cons _ _ => simp

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · intro result h_eq
    rw [h_eq]
    constructor
    · intro h_empty
      rw [h_empty, implementation_empty]
    · constructor
      · intro ⟨h_ne, h_mod3⟩
        have h_impl := implementation_nonempty lst h_ne
        simp [h_impl, h_mod3]
      · constructor
        · intro ⟨h_ne, h_mod4, h_not_mod3⟩
          have h_impl := implementation_nonempty lst h_ne
          simp [h_impl, h_not_mod3, h_mod4]
        · intro ⟨h_ne, h_not_mod3, h_not_mod4⟩
          have h_impl := implementation_nonempty lst h_ne
          simp [h_impl, h_not_mod3, h_not_mod4]