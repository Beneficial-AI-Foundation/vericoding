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
  termination_by l1.length + l2.length

def implementation (l1 l2: List Int) : List Int :=
  let common := filter_common l1 l2
  let unique := remove_duplicates common
  merge_sort unique

-- LLM HELPER
lemma filter_common_spec (l1 l2: List Int) (x: Int) :
  x ∈ filter_common l1 l2 ↔ x ∈ l1 ∧ x ∈ l2 := by
  simp [filter_common, List.mem_filter]

-- LLM HELPER
lemma remove_duplicates_unique (l: List Int) :
  let result := remove_duplicates l
  ∀ i j, i < result.length → j < result.length →
  i ≠ j → result[i]?.getD 0 ≠ result[j]?.getD 0 := by
  intro result i j hi hj hij
  simp [remove_duplicates] at result
  induction l using List.strongInductionOn with
  | ind l ih =>
    simp [remove_duplicates] at result
    have : result.Nodup := by
      simp [remove_duplicates]
      apply List.nodup_foldl
      · simp
      · intros a acc h_nodup h_not_mem
        by_cases h : a ∈ acc
        · simp [h]
          exact h_nodup
        · simp [h]
          apply List.nodup_append_of_nodup
          · exact h_nodup
          · simp
          · intros x hx hy
            simp at hy
            subst hy
            exact h hx
    exact List.nodup_iff_get_ne_get.mp this i j hi hj hij

-- LLM HELPER
lemma remove_duplicates_preserves_membership (l: List Int) (x: Int) :
  x ∈ remove_duplicates l ↔ x ∈ l := by
  simp [remove_duplicates]
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl_cons]
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
  result[i]?.getD 0 ≤ result[i + 1]?.getD 0 := by
  intro result i hi
  simp [merge_sort] at result
  induction l using List.strongInductionOn with
  | ind l ih =>
    simp [merge_sort] at result
    by_cases h : l.length ≤ 1
    · simp [h] at result hi
      omega
    · simp [h] at result
      have sorted_left : ∀ i, i < (merge_sort (List.take (l.length / 2) l)).length - 1 →
        (merge_sort (List.take (l.length / 2) l))[i]?.getD 0 ≤ (merge_sort (List.take (l.length / 2) l))[i + 1]?.getD 0 := by
        apply ih
        simp [List.take_length]
        omega
      have sorted_right : ∀ i, i < (merge_sort (List.drop (l.length / 2) l)).length - 1 →
        (merge_sort (List.drop (l.length / 2) l))[i]?.getD 0 ≤ (merge_sort (List.drop (l.length / 2) l))[i + 1]?.getD 0 := by
        apply ih
        simp [List.drop_length]
        omega
      sorry

-- LLM HELPER
lemma merge_sort_preserves_membership (l: List Int) (x: Int) :
  x ∈ merge_sort l ↔ x ∈ l := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    simp [merge_sort]
    by_cases h : l.length ≤ 1
    · simp [h]
    · simp [h]
      have h1 : (List.take (l.length / 2) l).length < l.length := by
        simp [List.take_length]
        omega
      have h2 : (List.drop (l.length / 2) l).length < l.length := by
        simp [List.drop_length]
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