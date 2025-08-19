import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

def implementation (lst: List Int) : Int := 
  match lst with
  | [] => 0
  | [_] => 0
  | _ :: b :: rest =>
    if b % 2 = 1 then
      b + implementation rest
    else
      implementation rest

-- LLM HELPER
lemma list_drop_zero (lst: List Int) : lst.drop 0 = lst := by
  rfl

-- LLM HELPER
lemma list_drop_two (a b : Int) (rest : List Int) : (a :: b :: rest).drop 2 = rest := by
  rfl

-- LLM HELPER
lemma list_get_one (a b : Int) (rest : List Int) : (a :: b :: rest)[1]! = b := by
  rfl

-- LLM HELPER
lemma list_length_cons (a : Int) (lst : List Int) : (a :: lst).length = lst.length + 1 := by
  rfl

-- LLM HELPER
lemma list_length_ge_two (a b : Int) (rest : List Int) : (a :: b :: rest).length ≥ 2 := by
  simp [List.length]
  omega

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · intro h i hi
    constructor
    · intro h_len
      cases' lst with head tail
      · contradiction
      · cases' tail with head' tail'
        · simp [implementation]
        · simp at h_len
    · intro h_succ
      cases' lst with head tail
      · contradiction  
      · cases' tail with head' tail'
        · simp at h_succ
        · cases' i with i'
          · simp at hi
            simp [List.drop, implementation]
            constructor
            · intro h_odd
              simp [h_odd]
              cases' tail' with head'' tail''
              · simp [implementation]
              · simp [implementation]
                by_cases h_even : head'' % 2 = 1
                · simp [h_even]
                · simp [h_even]
            · intro h_even
              simp [h_even]
              cases' tail' with head'' tail''
              · simp [implementation]
              · simp [implementation]
                by_cases h_odd : head'' % 2 = 1
                · simp [h_odd]
                · simp [h_odd]
          · cases' i' with i''
            · simp at hi
              simp [List.drop, implementation]
              constructor
              · intro h_odd
                cases' tail' with head'' tail''
                · simp [implementation]
                · simp [implementation]
                  by_cases h_even : head'' % 2 = 1
                  · simp [h_even]
                  · simp [h_even]
              · intro h_even
                cases' tail' with head'' tail''
                · simp [implementation]
                · simp [implementation]
                  by_cases h_odd : head'' % 2 = 1
                  · simp [h_odd]
                  · simp [h_odd]
            · simp at hi
              have h_len : (head :: head' :: tail').length = tail'.length + 2 := by simp [List.length]
              rw [h_len] at hi
              omega