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

-- LLM HELPER
def implementation (lst: List Int) : Int :=
  match lst with
  | [] => 0
  | [_] => 0
  | _ :: x :: xs => if x % 2 = 1 then x + implementation xs else implementation xs

-- LLM HELPER
theorem implementation_empty : implementation [] = 0 := by
  simp [implementation]

-- LLM HELPER
theorem implementation_single (x : Int) : implementation [x] = 0 := by
  simp [implementation]

-- LLM HELPER
theorem implementation_cons_odd (x y : Int) (xs : List Int) (h : y % 2 = 1) :
  implementation (x :: y :: xs) = y + implementation xs := by
  simp [implementation, h]

-- LLM HELPER
theorem implementation_cons_even (x y : Int) (xs : List Int) (h : y % 2 = 0) :
  implementation (x :: y :: xs) = implementation xs := by
  simp [implementation, h]

-- LLM HELPER
theorem implementation_drop_cons (x : Int) (xs : List Int) :
  implementation (List.drop 1 (x :: xs)) = implementation xs := by
  simp [List.drop]

-- LLM HELPER
theorem implementation_drop_cons_cons (x y : Int) (xs : List Int) :
  implementation (List.drop 2 (x :: y :: xs)) = implementation xs := by
  simp [List.drop]

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
          exact implementation_single hd
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
            have h_drop : List.drop i (hd :: hd2 :: tl2) = 
              if i = 0 then hd :: hd2 :: tl2 else hd2 :: tl2 := by
              cases' h_i.1 with h0
              · simp [List.drop]
              · cases' h0 with h1
                · simp [List.drop]
                · omega
            cases' h_i.1 with h0
            · simp [h_drop]
              rw [implementation_cons_odd]
              · simp [List.get!]
                by_cases h_empty : tl2 = []
                · simp [h_empty, List.length]
                · simp [List.length]
                  rw [implementation_drop_cons_cons]
              · simp [List.get!, h_odd]
            · cases' h0 with h1
              · simp [h_drop]
                rw [implementation_cons_even]
                · simp [List.get!]
                  by_cases h_empty : tl2 = []
                  · simp [h_empty, List.length]
                  · simp [List.length]
                    rw [implementation_drop_cons_cons]
                · simp [List.get!]
                  have h_even : hd2 % 2 = 0 := by
                    by_contra h_not_even
                    simp at h_not_even
                    have h_odd_alt : hd2 % 2 = 1 := by
                      have : hd2 % 2 = 0 ∨ hd2 % 2 = 1 := Int.mod_two_eq_zero_or_one hd2
                      cases this with
                      | inl h => contradiction
                      | inr h => exact h
                    rw [h_odd_alt] at h_odd
                    contradiction
                  exact h_even
              · omega
          · intro h_even
            have h_drop : List.drop i (hd :: hd2 :: tl2) = 
              if i = 0 then hd :: hd2 :: tl2 else hd2 :: tl2 := by
              cases' h_i.1 with h0
              · simp [List.drop]
              · cases' h0 with h1
                · simp [List.drop]
                · omega
            cases' h_i.1 with h0
            · simp [h_drop]
              rw [implementation_cons_even]
              · simp [List.get!]
                by_cases h_empty : tl2 = []
                · simp [h_empty, List.length]
                · simp [List.length]
                  rw [implementation_drop_cons_cons]
              · simp [List.get!, h_even]
            · cases' h0 with h1
              · simp [h_drop]
                rw [implementation_cons_odd]
                · simp [List.get!]
                  by_cases h_empty : tl2 = []
                  · simp [h_empty, List.length]
                  · simp [List.length]
                    rw [implementation_drop_cons_cons]
                · simp [List.get!]
                  have h_odd : hd2 % 2 = 1 := by
                    by_contra h_not_odd
                    simp at h_not_odd
                    have h_even_alt : hd2 % 2 = 0 := by
                      have : hd2 % 2 = 0 ∨ hd2 % 2 = 1 := Int.mod_two_eq_zero_or_one hd2
                      cases this with
                      | inl h => exact h
                      | inr h => contradiction
                    rw [h_even_alt] at h_even
                    contradiction
                  exact h_odd
              · omega