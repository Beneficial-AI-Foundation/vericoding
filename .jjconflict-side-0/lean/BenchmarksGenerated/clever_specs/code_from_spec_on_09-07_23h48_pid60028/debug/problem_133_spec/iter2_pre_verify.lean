def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(lst: List Rat) :=
-- spec
let spec (result: Int) :=
  (lst = [] → result = 0) ∧
  (lst ≠ [] → 0 ≤ result - lst.get! 0 ^2 ∧ (impl (lst.drop 1) = (result - lst.get! 0 ^2)))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

def implementation (lst: List Rat) : Int :=
  match lst with
  | [] => 0
  | h :: t => h^2 + implementation t

-- LLM HELPER
lemma implementation_empty : implementation [] = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (h : Rat) (t : List Rat) : 
  implementation (h :: t) = h^2 + implementation t := by
  simp [implementation]

-- LLM HELPER
lemma list_head_cons (h : Rat) (t : List Rat) : 
  (h :: t).get! 0 = h := by
  simp [List.get!]

-- LLM HELPER
lemma list_drop_one_cons (h : Rat) (t : List Rat) : 
  (h :: t).drop 1 = t := by
  simp [List.drop]

-- LLM HELPER
lemma ne_empty_cons (h : Rat) (t : List Rat) : 
  h :: t ≠ [] := by
  simp

theorem correctness
(lst: List Rat)
: problem_spec implementation lst := by
  cases lst with
  | nil => 
    use 0
    constructor
    · exact implementation_empty
    · constructor
      · intro h
        rfl
      · intro h
        exfalso
        exact h rfl
  | cons h t =>
    use h^2 + implementation t
    constructor
    · exact implementation_cons h t
    · constructor
      · intro h_contra
        exfalso
        exact ne_empty_cons h t h_contra
      · intro _
        constructor
        · simp [Int.le_refl]
        · rw [list_head_cons, list_drop_one_cons]
          simp [Int.add_sub_cancel]