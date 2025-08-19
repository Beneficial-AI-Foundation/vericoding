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

-- LLM HELPER
theorem implementation_drop_even (hd : Int) (hd2 : Int) (tl2 : List Int) (i : Nat) :
  i < (hd :: hd2 :: tl2).length →
  i % 2 = 0 →
  hd2 % 2 = 0 →
  implementation ((hd :: hd2 :: tl2).drop i) = 
  if i + 2 < (hd :: hd2 :: tl2).length then implementation ((hd :: hd2 :: tl2).drop (i + 2)) else 0 := by
  intro h_len h_even h_hd2_even
  cases' Nat.eq_zero_or_pos i with h_zero h_pos
  · simp [h_zero, List.drop, implementation, h_hd2_even]
    by_cases h_empty : tl2 = []
    · simp [h_empty, List.length]
    · simp [List.length]
      rfl
  · have h_i_eq : i = 1 := by
      have h_lt : i < (hd :: hd2 :: tl2).length := h_len
      simp [List.length] at h_lt
      have h_odd_even : i % 2 = 1 ∨ i % 2 = 0 := Nat.mod_two_eq_zero_or_one i
      cases h_odd_even with
      | inl h_odd => 
        rw [h_even] at h_odd
        simp at h_odd
      | inr h_even_check => 
        have h_le : i ≤ 2 := by omega
        have h_pos : 0 < i := h_pos
        have h_ne_zero : i ≠ 0 := Nat.ne_of_gt h_pos
        have h_cases : i = 1 ∨ i = 2 := by omega
        cases h_cases with
        | inl h_one => exact h_one
        | inr h_two => 
          rw [h_two] at h_even
          simp at h_even
    simp [h_i_eq, List.drop, implementation]
    cases' tl2 with hd3 tl3
    · simp [List.length]
    · simp [List.length]
      rw [h_hd2_even]
      simp

-- LLM HELPER
theorem implementation_drop_odd (hd : Int) (hd2 : Int) (tl2 : List Int) (i : Nat) :
  i < (hd :: hd2 :: tl2).length →
  i % 2 = 0 →
  hd2 % 2 = 1 →
  implementation ((hd :: hd2 :: tl2).drop i) = 
  hd2 + if i + 2 < (hd :: hd2 :: tl2).length then implementation ((hd :: hd2 :: tl2).drop (i + 2)) else 0 := by
  intro h_len h_even h_hd2_odd
  cases' Nat.eq_zero_or_pos i with h_zero h_pos
  · simp [h_zero, List.drop, implementation, h_hd2_odd]
    by_cases h_empty : tl2 = []
    · simp [h_empty, List.length]
    · simp [List.length]
      rfl
  · have h_i_eq : i = 1 := by
      have h_lt : i < (hd :: hd2 :: tl2).length := h_len
      simp [List.length] at h_lt
      have h_odd_even : i % 2 = 1 ∨ i % 2 = 0 := Nat.mod_two_eq_zero_or_one i
      cases h_odd_even with
      | inl h_odd => 
        rw [h_even] at h_odd
        simp at h_odd
      | inr h_even_check => 
        have h_le : i ≤ 2 := by omega
        have h_pos : 0 < i := h_pos
        have h_ne_zero : i ≠ 0 := Nat.ne_of_gt h_pos
        have h_cases : i = 1 ∨ i = 2 := by omega
        cases h_cases with
        | inl h_one => exact h_one
        | inr h_two => 
          rw [h_two] at h_even
          simp at h_even
    simp [h_i_eq, List.drop, implementation]
    cases' tl2 with hd3 tl3
    · simp [List.length]
    · simp [List.length]
      rw [h_hd2_odd]
      simp

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
            rw [get_getD_eq (hd :: hd2 :: tl2) (i + 1) (by omega)]
            simp [List.get!] at h_odd
            have h_hd2_odd : hd2 % 2 = 1 := by
              cases' Nat.eq_zero_or_pos i with h_zero h_pos
              · simp [h_zero] at h_odd
                exact h_odd
              · have h_i_eq : i = 1 := by omega
                simp [h_i_eq, List.get] at h_odd
                exact h_odd
            exact implementation_drop_odd hd hd2 tl2 i (by omega) h_i.2 h_hd2_odd
          · intro h_even
            rw [get_getD_eq (hd :: hd2 :: tl2) (i + 1) (by omega)]
            simp [List.get!] at h_even
            have h_hd2_even : hd2 % 2 = 0 := by
              cases' Nat.eq_zero_or_pos i with h_zero h_pos
              · simp [h_zero] at h_even
                exact h_even
              · have h_i_eq : i = 1 := by omega
                simp [h_i_eq, List.get] at h_even
                exact h_even
            exact implementation_drop_even hd hd2 tl2 i (by omega) h_i.2 h_hd2_even