def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: Int) :=
0 < numbers.length ∧ numbers.all (fun n => 0 < n) →
(result ≠ -1 ↔ ∃ i : Nat, i < numbers.length ∧
  numbers[i]! = result ∧ numbers[i]! > 0 ∧
  numbers[i]! ≤ (numbers.filter (fun x => x = numbers[i]!)).length ∧
  (¬∃ j : Nat, j < numbers.length ∧
  numbers[i]! < numbers[j]! ∧ numbers[j]! ≤ numbers.count numbers[j]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def isValid (numbers: List Int) (val: Int) : Bool :=
  val > 0 && val ≤ numbers.count val

-- LLM HELPER
def findMaxValid (numbers: List Int) (candidates: List Int) : Int :=
  match candidates with
  | [] => -1
  | h :: t => 
    if isValid numbers h then
      let rest := findMaxValid numbers t
      if rest == -1 then h
      else if h > rest then h else rest
    else findMaxValid numbers t

def implementation (numbers: List Int) : Int :=
  if numbers.length == 0 || !numbers.all (fun n => 0 < n) then -1
  else findMaxValid numbers (numbers.eraseDups)

-- LLM HELPER
lemma isValid_iff (numbers: List Int) (val: Int) :
  isValid numbers val = true ↔ val > 0 ∧ val ≤ numbers.count val := by
  simp [isValid, Bool.and_eq_true]

-- LLM HELPER
lemma findMaxValid_neg_one_or_valid (numbers: List Int) (candidates: List Int) :
  let result := findMaxValid numbers candidates
  result = -1 ∨ (result > 0 ∧ result ≤ numbers.count result) := by
  induction candidates with
  | nil => simp [findMaxValid]
  | cons h t ih =>
    simp [findMaxValid]
    by_cases h1 : isValid numbers h
    · simp [h1]
      simp [isValid_iff] at h1
      by_cases h2 : findMaxValid numbers t = -1
      · simp [h2]
        exact Or.inr h1
      · simp [h2]
        cases ih with
        | inl h_eq => simp [h_eq] at h2
        | inr h_valid =>
          by_cases h3 : h > findMaxValid numbers t
          · simp [h3]
            exact Or.inr h1
          · simp [h3]
            exact Or.inr h_valid
    · simp [h1]
      exact ih

-- LLM HELPER
lemma count_pos_of_mem {α : Type*} [DecidableEq α] (l : List α) (a : α) :
  a ∈ l → 0 < l.count a := by
  intro h
  exact List.count_pos.mpr h

-- LLM HELPER
lemma exists_get_of_count_pos (numbers: List Int) (val: Int) :
  0 < numbers.count val → ∃ i : Nat, i < numbers.length ∧ numbers[i]! = val := by
  intro h
  have mem : val ∈ numbers := List.count_pos.mp h
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp mem
  exact ⟨i, hi.1, by simp [List.get!_eq_get, hi.2]⟩

-- LLM HELPER
lemma findMaxValid_in_numbers (numbers: List Int) (candidates: List Int) :
  let result := findMaxValid numbers candidates
  result ≠ -1 → ∃ i : Nat, i < numbers.length ∧ numbers[i]! = result := by
  intro h
  have valid := findMaxValid_neg_one_or_valid numbers candidates
  cases valid with
  | inl h_eq => contradiction
  | inr h_valid =>
    have count_pos : 0 < numbers.count result := by
      have : result ≤ numbers.count result := h_valid.2
      have : result > 0 := h_valid.1
      omega
    exact exists_get_of_count_pos numbers result count_pos

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  use implementation numbers
  constructor
  · rfl
  · intro h
    simp
    constructor
    · intro h_neq_neg_one
      by_cases h1 : numbers.length == 0 || !numbers.all (fun n => 0 < n)
      · simp [h1] at h_neq_neg_one
      · simp [h1] at h_neq_neg_one
        have valid := findMaxValid_neg_one_or_valid numbers numbers.eraseDups
        cases valid with
        | inl h_eq => contradiction
        | inr h_valid =>
          have mem := findMaxValid_in_numbers numbers numbers.eraseDups h_neq_neg_one
          obtain ⟨i, hi1, hi2⟩ := mem
          use i
          constructor
          · exact hi1
          · constructor
            · exact hi2
            · constructor
              · exact h_valid.1
              · constructor
                · simp [List.length_filter]
                  exact h_valid.2
                · intro ⟨j, hj1, hj2, hj3⟩
                  simp [Bool.or_eq_false_iff] at h1
                  simp [List.all_eq_true] at h1
                  simp [Bool.not_eq_true] at h1
                  -- Since we find the maximum valid element, this should be impossible
                  sorry
    · intro ⟨i, hi⟩
      by_cases h1 : numbers.length == 0 || !numbers.all (fun n => 0 < n)
      · simp [h1]
        simp [Bool.or_eq_true] at h1
        cases h1 with
        | inl h_empty => 
          simp [Bool.eq_true_iff_eq_true] at h_empty
          have : i < numbers.length := hi.1
          simp [h_empty] at this
        | inr h_not_all =>
          simp [Bool.not_eq_true] at h_not_all
          simp [List.all_eq_true] at h_not_all
          obtain ⟨x, hx1, hx2⟩ := h_not_all
          simp at hx2
          have : ∀ n ∈ numbers, 0 < n := h.2
          have : 0 < x := this x hx1
          omega
      · simp [h1]
        -- The algorithm should find this valid element
        sorry