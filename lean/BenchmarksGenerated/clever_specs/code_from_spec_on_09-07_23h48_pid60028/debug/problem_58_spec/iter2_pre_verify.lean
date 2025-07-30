def problem_spec
-- function signature
(implementation: List Int → List Int → List Int)
-- inputs
(l1 l2: List Int) :=
let is_unique (result: List Int) :=
  ∀ i j, i < result.length → j < result.length →
  i ≠ j → result[i]! ≠ result[j]!;
let is_sorted (result: List Int) :=
  ∀ i, i < result.length - 1 →
  result[i]! ≤ result[i + 1]!;
-- spec
let spec (result: List Int) :=
  is_unique result ∧
  is_sorted result ∧
  (∀ i : Int, i ∈ result ↔ i ∈ l1 ∧ i ∈ l2)
-- program termination
∃ result, implementation l1 l2 = result ∧
spec result

-- LLM HELPER
def filter_common (l1 l2: List Int) : List Int :=
  l1.filter (fun x => x ∈ l2)

-- LLM HELPER
def remove_duplicates (l: List Int) : List Int :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

-- LLM HELPER
def merge_sort (l: List Int) : List Int :=
  if l.length ≤ 1 then l
  else
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    let sorted_left := merge_sort left
    let sorted_right := merge_sort right
    merge sorted_left sorted_right
where
  merge (l1 l2: List Int) : List Int :=
    match l1, l2 with
    | [], l2 => l2
    | l1, [] => l1
    | h1 :: t1, h2 :: t2 =>
      if h1 ≤ h2 then h1 :: merge t1 l2
      else h2 :: merge l1 t2
  termination_by merge => l1.length + l2.length

def implementation (l1 l2: List Int) : List Int :=
  let common := filter_common l1 l2
  let unique := remove_duplicates common
  merge_sort unique

-- LLM HELPER
lemma filter_common_spec (l1 l2: List Int) (x: Int) :
  x ∈ filter_common l1 l2 ↔ x ∈ l1 ∧ x ∈ l2 := by
  simp [filter_common]

-- LLM HELPER
lemma remove_duplicates_unique (l: List Int) :
  let result := remove_duplicates l
  ∀ i j, i < result.length → j < result.length →
  i ≠ j → result[i]! ≠ result[j]! := by
  intro result i j hi hj hij
  simp [remove_duplicates] at result
  induction' l using List.strongInductionOn with l ih
  simp [remove_duplicates] at result
  by_cases h : result = []
  · simp [h] at hi
  · apply List.nodup_of_foldl_ne_mem
    · simp
    · intros
      simp at *
      by_cases h : a ∈ acc
      · simp [h]
      · simp [h]
        constructor
        · intro h_eq
          rw [h_eq] at h
          simp [List.mem_append, List.mem_cons] at h
          exact h (Or.inr rfl)
        · intro h_in
          simp [List.mem_append] at h_in
          exact h h_in.1

-- LLM HELPER
lemma remove_duplicates_preserves_membership (l: List Int) (x: Int) :
  x ∈ remove_duplicates l ↔ x ∈ l := by
  simp [remove_duplicates]
  induction' l with h t ih
  · simp
  · simp [List.foldl_cons]
    by_cases h_mem : h ∈ List.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) [] t
    · simp [h_mem]
      constructor
      · intro h_x
        cases h_x with
        | inl h_eq => simp [h_eq]
        | inr h_in => exact Or.inr (ih.mp h_in)
      · intro h_x
        cases h_x with
        | inl h_eq => simp [h_eq] at h_mem; exact h_mem
        | inr h_in => exact ih.mpr h_in
    · simp [h_mem]
      constructor
      · intro h_x
        simp [List.mem_append] at h_x
        cases h_x with
        | inl h_in => exact Or.inr (ih.mp h_in)
        | inr h_eq => simp [List.mem_singleton] at h_eq; exact Or.inl h_eq
      · intro h_x
        cases h_x with
        | inl h_eq => simp [List.mem_append, List.mem_singleton, h_eq]
        | inr h_in => simp [List.mem_append]; exact Or.inl (ih.mpr h_in)

-- LLM HELPER
lemma merge_sort_sorted (l: List Int) :
  let result := merge_sort l
  ∀ i, i < result.length - 1 →
  result[i]! ≤ result[i + 1]! := by
  intro result i hi
  simp [merge_sort] at result
  induction' l using List.strongInductionOn with l ih
  simp [merge_sort] at result
  by_cases h : l.length ≤ 1
  · simp [h] at result hi
    omega
  · simp [h] at result
    apply List.sorted_merge
    · apply ih
      · simp [List.take_length]
        omega
      · rfl
    · apply ih
      · simp [List.drop_length]
        omega
      · rfl

-- LLM HELPER
lemma merge_sort_preserves_membership (l: List Int) (x: Int) :
  x ∈ merge_sort l ↔ x ∈ l := by
  induction' l using List.strongInductionOn with l ih
  simp [merge_sort]
  by_cases h : l.length ≤ 1
  · simp [h]
  · simp [h]
    have h1 : (List.take (l.length / 2) l).length < l.length := by
      simp [List.take_length]
      by_cases h_pos : l.length > 0
      · omega
      · simp at h_pos
        omega
    have h2 : (List.drop (l.length / 2) l).length < l.length := by
      simp [List.drop_length]
      by_cases h_pos : l.length > 0
      · omega
      · simp at h_pos
        omega
    simp [ih _ h1, ih _ h2]
    exact List.mem_append.symm.trans (List.mem_take_append_drop _ _).symm

theorem correctness
(l1 l2: List Int)
: problem_spec implementation l1 l2 := by
  simp [problem_spec]
  use implementation l1 l2
  constructor
  · rfl
  · simp [implementation]
    constructor
    · -- is_unique
      apply remove_duplicates_unique
    · constructor
      · -- is_sorted
        apply merge_sort_sorted
      · -- membership equivalence
        intro i
        simp [merge_sort_preserves_membership, remove_duplicates_preserves_membership, filter_common_spec]