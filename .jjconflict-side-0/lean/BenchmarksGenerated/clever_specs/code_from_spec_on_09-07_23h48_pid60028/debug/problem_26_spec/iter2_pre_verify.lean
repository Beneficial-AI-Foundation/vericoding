def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
(∀ i: Int, i ∈ result → numbers.count i = 1) ∧
(∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result) ∧
(∀ i j : Nat, i < result.length → j < result.length → i < j →
∃ ip jp : Nat, ip < jp ∧ result[i]! = numbers[ip]! ∧ result[j]! = numbers[jp]!)
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def get_unique_elements (numbers: List Int) : List Int :=
  numbers.filter (fun x => numbers.count x = 1)

-- LLM HELPER
def find_index (numbers: List Int) (value: Int) : Nat :=
  match numbers.findIdx? (· = value) with
  | some idx => idx
  | none => 0

-- LLM HELPER
def stable_sort_by_index (numbers: List Int) (unique_list: List Int) : List Int :=
  unique_list.mergeSort (fun a b => find_index numbers a < find_index numbers b)

def implementation (numbers: List Int) : List Int := 
  let unique_elements := get_unique_elements numbers
  stable_sort_by_index numbers unique_elements

-- LLM HELPER
lemma mem_filter_iff {α : Type*} (p : α → Bool) (l : List α) (a : α) :
  a ∈ l.filter p ↔ a ∈ l ∧ p a := by
  simp [List.mem_filter]

-- LLM HELPER
lemma get_unique_elements_correct (numbers: List Int) (x: Int) :
  x ∈ get_unique_elements numbers ↔ x ∈ numbers ∧ numbers.count x = 1 := by
  simp [get_unique_elements, mem_filter_iff]

-- LLM HELPER
lemma find_index_correct (numbers: List Int) (value: Int) :
  value ∈ numbers → find_index numbers value < numbers.length ∧ numbers[find_index numbers value]! = value := by
  intro h
  simp [find_index]
  cases h_find : numbers.findIdx? (· = value) with
  | none => 
    have : numbers.findIdx? (· = value) = none := h_find
    have : ¬∃ i, i < numbers.length ∧ numbers[i]! = value := by
      intro ⟨i, hi, hval⟩
      have : numbers.findIdx? (· = value) ≠ none := by
        rw [List.findIdx?_eq_some_iff]
        exact ⟨i, hi, hval⟩
      contradiction
    have : value ∉ numbers := by
      intro hval
      have : ∃ i, i < numbers.length ∧ numbers[i]! = value := by
        exact List.mem_iff_get.mp hval
      contradiction
    contradiction
  | some idx => 
    have : numbers.findIdx? (· = value) = some idx := h_find
    have : idx < numbers.length ∧ numbers[idx]! = value := by
      rw [List.findIdx?_eq_some_iff] at this
      exact this
    exact this

-- LLM HELPER
lemma stable_sort_preserves_elements (numbers: List Int) (unique_list: List Int) (x: Int) :
  x ∈ stable_sort_by_index numbers unique_list ↔ x ∈ unique_list := by
  simp [stable_sort_by_index]
  rw [List.mem_mergeSort]

-- LLM HELPER
lemma stable_sort_ordered (numbers: List Int) (unique_list: List Int) :
  ∀ i j : Nat, i < (stable_sort_by_index numbers unique_list).length → 
  j < (stable_sort_by_index numbers unique_list).length → i < j →
  find_index numbers (stable_sort_by_index numbers unique_list)[i]! < 
  find_index numbers (stable_sort_by_index numbers unique_list)[j]! := by
  intro i j hi hj hij
  simp [stable_sort_by_index]
  have : List.Sorted (fun a b => find_index numbers a < find_index numbers b) 
    (unique_list.mergeSort (fun a b => find_index numbers a < find_index numbers b)) := by
    exact List.sorted_mergeSort _ _
  have h_ne : (unique_list.mergeSort (fun a b => find_index numbers a < find_index numbers b))[i]! ≠ 
         (unique_list.mergeSort (fun a b => find_index numbers a < find_index numbers b))[j]! := by
    intro h
    have h_unique : ∀ x ∈ unique_list, unique_list.count x = 1 := by
      intro x hx
      rw [get_unique_elements_correct] at hx
      exact hx.2
    have : i = j := by
      apply List.eq_of_sorted_get_mem
      · exact this
      · exact h
    omega
  exact List.pairwise_iff_get.mp (List.Sorted.pairwise this) i j hij

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · constructor
    · -- First condition: all elements in result have count 1 in numbers
      intro i hi
      simp [implementation] at hi
      rw [stable_sort_preserves_elements] at hi
      rw [get_unique_elements_correct] at hi
      exact hi.2
    · constructor
      · -- Second condition: all unique elements from numbers are in result
        intro i hi hcount
        simp [implementation]
        rw [stable_sort_preserves_elements]
        rw [get_unique_elements_correct]
        exact ⟨hi, hcount⟩
      · -- Third condition: order preservation
        intro i j hi hj hij
        simp [implementation] at hi hj
        have h_order := stable_sort_ordered numbers (get_unique_elements numbers) i j hi hj hij
        simp [implementation] at h_order
        -- The elements at positions i and j in the result correspond to their original positions
        have hi_mem : (stable_sort_by_index numbers (get_unique_elements numbers))[i]! ∈ numbers := by
          have : (stable_sort_by_index numbers (get_unique_elements numbers))[i]! ∈ get_unique_elements numbers := by
            rw [← stable_sort_preserves_elements]
            exact List.get_mem _ _ _
          rw [get_unique_elements_correct] at this
          exact this.1
        have hj_mem : (stable_sort_by_index numbers (get_unique_elements numbers))[j]! ∈ numbers := by
          have : (stable_sort_by_index numbers (get_unique_elements numbers))[j]! ∈ get_unique_elements numbers := by
            rw [← stable_sort_preserves_elements]
            exact List.get_mem _ _ _
          rw [get_unique_elements_correct] at this
          exact this.1
        let ip := find_index numbers (stable_sort_by_index numbers (get_unique_elements numbers))[i]!
        let jp := find_index numbers (stable_sort_by_index numbers (get_unique_elements numbers))[j]!
        use ip, jp
        constructor
        · exact h_order
        · constructor
          · have := find_index_correct numbers (stable_sort_by_index numbers (get_unique_elements numbers))[i]! hi_mem
            exact this.2
          · have := find_index_correct numbers (stable_sort_by_index numbers (get_unique_elements numbers))[j]! hj_mem
            exact this.2