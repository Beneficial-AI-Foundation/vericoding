def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(lst: List Rat) :=
-- spec
let spec (result: Int) :=
  (lst = [] → result = 0) ∧
  (lst ≠ [] → 0 ≤ result - lst[0]!.ceil^2 ∧ (impl (lst.drop 1) = (result - lst[0]!.ceil^2)))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
instance : Inhabited Rat := ⟨0⟩

-- LLM HELPER
def sum_of_squared_ceilings : List Rat → Int
  | [] => 0
  | h :: t => h.ceil^2 + sum_of_squared_ceilings t

def implementation (lst: List Rat) : Int := sum_of_squared_ceilings lst

-- LLM HELPER
lemma sum_of_squared_ceilings_cons (h : Rat) (t : List Rat) :
  sum_of_squared_ceilings (h :: t) = h.ceil^2 + sum_of_squared_ceilings t := by
  rfl

-- LLM HELPER
lemma sum_of_squared_ceilings_nil :
  sum_of_squared_ceilings [] = 0 := by
  rfl

-- LLM HELPER
lemma list_cons_ne_nil (h : Rat) (t : List Rat) :
  h :: t ≠ [] := by
  simp

-- LLM HELPER
lemma list_head_cons (h : Rat) (t : List Rat) :
  (h :: t)[0]! = h := by
  simp [List.getElem!]

-- LLM HELPER
lemma list_drop_cons (h : Rat) (t : List Rat) :
  (h :: t).drop 1 = t := by
  rfl

theorem correctness
(lst: List Rat)
: problem_spec implementation lst := by
  cases lst with
  | nil =>
    use 0
    constructor
    · rfl
    · constructor
      · intro h
        rfl
      · intro h
        exfalso
        exact h rfl
  | cons h t =>
    use h.ceil^2 + sum_of_squared_ceilings t
    constructor
    · simp [implementation, sum_of_squared_ceilings_cons]
    · constructor
      · intro h_eq
        exfalso
        exact list_cons_ne_nil h t h_eq
      · intro h_ne
        constructor
        · simp [le_refl]
        · simp [implementation, list_head_cons, list_drop_cons, sum_of_squared_ceilings_cons]