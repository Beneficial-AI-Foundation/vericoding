def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Int) :=
  lst.length = 0 → result = 0 ∧
  lst.length > 0 →
    if lst.length > 1 then
      result = (if Even lst[1]! then lst[1]! else 0) + implementation (lst.drop 2)
    else
      result = (if Even lst[1]! then lst[1]! else 0)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def Even (n : Int) : Prop := ∃ k, n = 2 * k

-- LLM HELPER
instance (n : Int) : Decidable (Even n) := by
  unfold Even
  exact Int.decidable_exists_emod n 2

def implementation (lst: List Int) : Int :=
  match lst with
  | [] => 0
  | [_] => 0
  | _ :: x :: xs => (if Even x then x else 0) + implementation xs

-- LLM HELPER
lemma list_length_zero_iff_nil (lst : List Int) : lst.length = 0 ↔ lst = [] := by
  cases lst with
  | nil => simp
  | cons head tail => simp

-- LLM HELPER
lemma list_get_one_cons_cons (a b : Int) (xs : List Int) : (a :: b :: xs)[1]! = b := by
  simp [List.get!, List.get]

-- LLM HELPER
lemma list_drop_two_cons_cons (a b : Int) (xs : List Int) : (a :: b :: xs).drop 2 = xs := by
  simp [List.drop]

-- LLM HELPER
lemma single_element_case (head : Int) : 
  (if (head :: []).length > 1 then 
    (if Even (head :: [])[1]! then (head :: [])[1]! else 0) + implementation ((head :: []).drop 2)
  else 
    (if Even (head :: [])[1]! then (head :: [])[1]! else 0)) = 0 := by
  simp [List.length, List.get!, List.get]

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  exists implementation lst
  constructor
  · rfl
  · constructor
    · intro h
      rw [list_length_zero_iff_nil] at h
      rw [h]
      simp [implementation]
    · intro h
      cases lst with
      | nil => 
        simp at h
      | cons head tail =>
        cases tail with
        | nil =>
          simp [implementation]
          exact single_element_case head
        | cons second rest =>
          simp [implementation]
          simp at h
          rw [list_get_one_cons_cons, list_drop_two_cons_cons]