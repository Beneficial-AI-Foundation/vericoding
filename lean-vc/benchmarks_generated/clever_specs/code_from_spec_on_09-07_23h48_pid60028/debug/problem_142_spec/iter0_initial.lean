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

-- LLM HELPER
lemma take_length_minus_one (lst : List Int) (h : lst ≠ []) : 
  (lst.take (lst.length - 1)).length < lst.length := by
  cases lst with
  | nil => contradiction
  | cons head tail => 
    simp [List.take]
    cases tail with
    | nil => simp
    | cons _ _ => 
      simp [List.length]
      omega

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · unfold problem_spec
    simp
    cases h : lst = [] with
    | false => 
      simp [h]
      have h_ne : lst ≠ [] := by
        intro h_eq
        simp [h_eq] at h
      rw [implementation_nonempty lst h_ne]
      let last := lst.length - 1
      let lastElem := lst[last]!
      let rest := implementation (lst.take last)
      by_cases h3 : last % 3 = 0
      · simp [h3]
        constructor
        · intro h4
          simp [h4] at h3
          contradiction
        · intro h4
          simp [h4] at h3
          contradiction
      · simp [h3]
        by_cases h4 : last % 4 = 0
        · simp [h4, h3]
        · simp [h4, h3]
    | true => 
      simp [h, implementation_empty]