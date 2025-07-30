def problem_spec
-- function signature
(implementation: List Int → List String)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: List String) :=
  let digits: List String := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"];
  (forall s: String, (s ∈ result → s ∈ digits)) ∧
  (arr.length ≥ result.length) ∧
  (forall x: Nat, ((x: Int) ∈ arr ∧ 1 ≤ x ∧ x ≤ 9) → (digits[x-1]! ∈ result)) ∧
  (List.Sorted Int.le (List.map (fun (s: String) => (List.indexOf s digits) + 1) result).reverse)
-- program termination
∃ result, implementation arr = result ∧
spec result

-- LLM HELPER
def int_to_string (n: Int) : Option String :=
  let digits: List String := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  if 1 ≤ n ∧ n ≤ 9 then
    some (digits[n.natAbs - 1]!)
  else
    none

-- LLM HELPER
def filter_and_convert (arr: List Int) : List String :=
  arr.filterMap int_to_string

-- LLM HELPER
def sort_by_digit_value (strings: List String) : List String :=
  let digits: List String := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  let with_indices := strings.map (fun s => (s, List.indexOf s digits + 1))
  let sorted := with_indices.mergeSort (fun a b => a.2 ≥ b.2)
  sorted.map (fun p => p.1)

def implementation (arr: List Int) : List String := 
  sort_by_digit_value (filter_and_convert arr)

-- LLM HELPER
lemma int_to_string_valid (n: Int) : 
  ∀ s, int_to_string n = some s → s ∈ ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] := by
  intro s h
  unfold int_to_string at h
  split at h
  · simp at h
    rw [←h]
    simp [List.getElem_mem]
  · simp at h

-- LLM HELPER
lemma filter_and_convert_valid (arr: List Int) :
  ∀ s, s ∈ filter_and_convert arr → s ∈ ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] := by
  intro s h
  unfold filter_and_convert at h
  simp [List.mem_filterMap] at h
  obtain ⟨n, hn_mem, hn_some⟩ := h
  exact int_to_string_valid n s hn_some

-- LLM HELPER
lemma sort_preserves_membership (strings: List String) :
  ∀ s, s ∈ sort_by_digit_value strings ↔ s ∈ strings := by
  intro s
  unfold sort_by_digit_value
  simp [List.mem_map]
  constructor
  · intro h
    obtain ⟨p, hp_mem, hp_eq⟩ := h
    rw [←hp_eq]
    simp [List.mem_mergeSort] at hp_mem
    obtain ⟨t, ht_mem, ht_eq⟩ := hp_mem
    rw [←ht_eq.1]
    exact ht_mem
  · intro h
    use (s, List.indexOf s ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] + 1)
    constructor
    · simp [List.mem_mergeSort]
      use s
      simp [h]
    · simp

-- LLM HELPER
lemma filter_and_convert_length (arr: List Int) :
  (filter_and_convert arr).length ≤ arr.length := by
  unfold filter_and_convert
  exact List.length_filterMap_le _ _

-- LLM HELPER
lemma sort_preserves_length (strings: List String) :
  (sort_by_digit_value strings).length = strings.length := by
  unfold sort_by_digit_value
  simp [List.length_map, List.length_mergeSort]

-- LLM HELPER
lemma contains_valid_digits (arr: List Int) :
  ∀ x: Nat, ((x: Int) ∈ arr ∧ 1 ≤ x ∧ x ≤ 9) → 
  (["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"][x-1]! ∈ filter_and_convert arr) := by
  intro x h
  unfold filter_and_convert
  simp [List.mem_filterMap]
  use x
  constructor
  · exact h.1
  · unfold int_to_string
    simp [h.2.1, h.2.2]
    simp [Int.natAbs_of_nonneg (Int.le_trans (by norm_num : (0 : Int) ≤ 1) h.2.1)]

-- LLM HELPER
lemma implementation_sorted (arr: List Int) :
  List.Sorted Int.le (List.map (fun (s: String) => (List.indexOf s ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]) + 1) (implementation arr)).reverse := by
  unfold implementation
  unfold sort_by_digit_value
  simp [List.map_map]
  have h : List.Sorted Int.le (List.map (fun p => p.2) (List.mergeSort (fun a b => a.2 ≥ b.2) (List.map (fun s => (s, List.indexOf s ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] + 1)) (filter_and_convert arr)))).reverse := by
    simp [List.sorted_reverse]
    exact List.sorted_mergeSort_map_snd _ _
  exact h

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  use implementation arr
  constructor
  · rfl
  · constructor
    · intro s h
      unfold implementation at h
      rw [sort_preserves_membership] at h
      exact filter_and_convert_valid arr s h
    · constructor
      · unfold implementation
        rw [sort_preserves_length, ←filter_and_convert_length]
        exact Nat.le_refl _
      · constructor
        · intro x h
          unfold implementation
          rw [sort_preserves_membership]
          exact contains_valid_digits arr x h
        · exact implementation_sorted arr