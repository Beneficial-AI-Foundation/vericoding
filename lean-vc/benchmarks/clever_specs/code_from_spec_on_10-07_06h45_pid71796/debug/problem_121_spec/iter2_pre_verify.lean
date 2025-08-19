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
  | _ :: x :: xs => if x % 2 = 1 then x + implementation xs else implementation xs

-- LLM HELPER
theorem get_getD_eq (lst : List Int) (i : Nat) (h : i < lst.length) :
  lst[i]! = lst[i]?.getD 0 := by
  simp [List.get!, List.getD]
  rw [List.get?_eq_get]
  · simp
  · exact h

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · intro h_nonempty i h_i
    cases' lst with hd tl
    · contradiction
    · cases' tl with hd2 tl2
      · simp [List.length] at h_i
        have h_len : [hd].length = 1 := by simp
        constructor
        · intro _
          simp [implementation]
        · intro h_succ
          simp [List.length] at h_succ
          omega
      · simp [List.length] at h_i
        have h_len : (hd :: hd2 :: tl2).length ≠ 1 := by simp [List.length]; omega
        constructor
        · intro h_contra
          contradiction
        · intro h_succ
          simp [List.length] at h_succ
          constructor
          · intro h_odd
            have h_i_cases : i = 0 ∨ i = 1 := by omega
            cases h_i_cases with
            | inl h0 =>
              simp [h0, List.drop, implementation]
              rw [get_getD_eq]
              · simp [List.get!]
                simp [h_odd]
                by_cases h_empty : tl2 = []
                · simp [h_empty, List.length]
                · simp [List.length]
                  rw [← List.drop_drop]
                  simp [List.drop]
              · simp [List.length]
            | inr h1 =>
              simp [h1, List.drop, implementation]
              rw [get_getD_eq]
              · simp [List.get!]
                simp [h_odd]
                by_cases h_empty : tl2 = []
                · simp [h_empty, List.length]
                · simp [List.length]
                  rw [← List.drop_drop]
                  simp [List.drop]
              · simp [List.length]
          · intro h_even
            have h_i_cases : i = 0 ∨ i = 1 := by omega
            cases h_i_cases with
            | inl h0 =>
              simp [h0, List.drop, implementation]
              rw [get_getD_eq]
              · simp [List.get!]
                simp [h_even]
                by_cases h_empty : tl2 = []
                · simp [h_empty, List.length]
                · simp [List.length]
                  rw [← List.drop_drop]
                  simp [List.drop]
              · simp [List.length]
            | inr h1 =>
              simp [h1, List.drop, implementation]
              rw [get_getD_eq]
              · simp [List.get!]
                simp [h_even]
                by_cases h_empty : tl2 = []
                · simp [h_empty, List.length]
                · simp [List.length]
                  rw [← List.drop_drop]
                  simp [List.drop]
              · simp [List.length]