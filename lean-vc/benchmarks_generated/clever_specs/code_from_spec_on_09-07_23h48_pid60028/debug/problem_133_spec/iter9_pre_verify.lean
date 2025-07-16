def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(lst: List Rat) :=
-- spec
let spec (result: Int) :=
  (lst = [] → result = 0) ∧
  (lst ≠ [] → 0 ≤ result - lst[0]! ^ 2 ∧ (impl (lst.drop 1) = (result - lst[0]! ^ 2)))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
instance : Inhabited Rat := ⟨0⟩

-- LLM HELPER
instance : HPow Rat Nat Rat := ⟨fun r n => r ^ n⟩

-- LLM HELPER
instance : OfNat Rat n := ⟨(n : ℚ)⟩

-- LLM HELPER
def rat_to_int (r : Rat) : Int := r.floor

def implementation (lst: List Rat) : Int :=
  match lst with
  | [] => 0
  | h :: t => rat_to_int (h ^ 2) + implementation t

-- LLM HELPER
lemma implementation_empty : implementation [] = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (h : Rat) (t : List Rat) : 
  implementation (h :: t) = rat_to_int (h ^ 2) + implementation t := by
  simp [implementation]

-- LLM HELPER
lemma list_head_cons (h : Rat) (t : List Rat) : 
  (h :: t)[0]! = h := by
  simp [List.getElem!]

-- LLM HELPER
lemma list_drop_one_cons (h : Rat) (t : List Rat) : 
  (h :: t).drop 1 = t := by
  simp [List.drop]

-- LLM HELPER
lemma ne_empty_cons (h : Rat) (t : List Rat) : 
  h :: t ≠ [] := by
  simp

-- LLM HELPER
lemma rat_floor_le (r : Rat) : r.floor ≤ r := by
  exact Rat.floor_le r

-- LLM HELPER
lemma rat_pow_two_nonneg (r : Rat) : 0 ≤ r ^ 2 := by
  exact sq_nonneg r

-- LLM HELPER
lemma floor_sub_le (r : Rat) : 0 ≤ r - r.floor := by
  simp [Rat.sub_floor]
  exact Rat.sub_floor_div_mul_nonneg r 1

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
    use rat_to_int (h ^ 2) + implementation t
    constructor
    · exact implementation_cons h t
    · constructor
      · intro h_contra
        exfalso
        exact ne_empty_cons h t h_contra
      · intro _
        constructor
        · rw [list_head_cons]
          simp [rat_to_int]
          rw [Int.add_sub_cancel']
          exact le_refl 0
        · rw [list_head_cons, list_drop_one_cons]
          simp [rat_to_int]
          rw [Int.add_sub_cancel']
          rfl