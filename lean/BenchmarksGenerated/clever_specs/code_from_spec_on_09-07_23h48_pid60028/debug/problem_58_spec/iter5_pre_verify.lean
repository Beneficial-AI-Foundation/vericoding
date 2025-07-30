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
def merge (l1 l2: List Int) : List Int :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 =>
    if h1 ≤ h2 then 
      h1 :: merge t1 l2
    else 
      h2 :: merge l1 t2
  termination_by l1.length + l2.length

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
  termination_by l.length

def implementation (l1 l2: List Int) : List Int :=
  let common := filter_common l1 l2
  let unique := remove_duplicates common
  merge_sort unique

-- LLM HELPER
lemma filter_common_spec (l1 l2: List Int) (x: Int) :
  x ∈ filter_common l1 l2 ↔ x ∈ l1 ∧ x ∈ l2 := by
  simp [filter_common, List.mem_filter]

-- LLM HELPER
lemma remove_duplicates_nodup (l: List Int) :
  (remove_duplicates l).Nodup := by
  simp [remove_duplicates]
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl_cons]
    by_cases h_mem : h ∈ List.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) [] t
    · simp [h_mem]; exact ih
    · simp [h_mem]; exact List.nodup_append_of_nodup ih (List.nodup_singleton _) (fun _ h1 h2 => h_mem (List.mem_singleton.mp h2 ▸ h1))

-- LLM HELPER
lemma remove_duplicates_preserves_membership (l: List Int) (x: Int) :
  x ∈ remove_duplicates l ↔ x ∈ l := by
  simp [remove_duplicates]
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl_cons]
    by_cases h_mem : h ∈ List.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) [] t
    · simp [h_mem]; exact ⟨fun h => Or.inr (ih.mp h), fun h => match h with | Or.inl rfl => ih.mpr (List.mem_of_mem_filter h_mem) | Or.inr h => ih.mpr h⟩
    · simp [h_mem, List.mem_append, List.mem_singleton]; exact ⟨fun h => match h with | Or.inl h => Or.inr (ih.mp h) | Or.inr rfl => Or.inl rfl, fun h => match h with | Or.inl rfl => Or.inr rfl | Or.inr h => Or.inl (ih.mpr h)⟩

-- LLM HELPER
lemma merge_sort_preserves_membership (l: List Int) (x: Int) :
  x ∈ merge_sort l ↔ x ∈ l := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    simp [merge_sort]
    by_cases h : l.length ≤ 1
    · simp [h]
    · simp [h]
      have h1 : (List.take (l.length / 2) l).length < l.length := by simp [List.take_length]; omega
      have h2 : (List.drop (l.length / 2) l).length < l.length := by simp [List.drop_length]; omega
      have merge_preserves : ∀ l1 l2, x ∈ merge l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
        intro l1 l2
        induction l1, l2 using merge.induct with
        | case1 l2 => simp [merge]
        | case2 l1 => simp [merge]
        | case3 h1 t1 h2 t2 =>
          simp [merge]
          by_cases h_le : h1 ≤ h2
          · simp [h_le]; exact ⟨fun h => match h with | Or.inl rfl => Or.inl (Or.inl rfl) | Or.inr h => match (this t1 (h2 :: t2)).mp h with | Or.inl h => Or.inl (Or.inr h) | Or.inr h => Or.inr h, fun h => match h with | Or.inl (Or.inl rfl) => Or.inl rfl | Or.inl (Or.inr h) => Or.inr ((this t1 (h2 :: t2)).mpr (Or.inl h)) | Or.inr h => Or.inr ((this t1 (h2 :: t2)).mpr (Or.inr h))⟩
          · simp [h_le]; exact ⟨fun h => match h with | Or.inl rfl => Or.inr (Or.inl rfl) | Or.inr h => match (this (h1 :: t1) t2).mp h with | Or.inl h => Or.inl h | Or.inr h => Or.inr (Or.inr h), fun h => match h with | Or.inl h => Or.inr ((this (h1 :: t1) t2).mpr (Or.inl h)) | Or.inr (Or.inl rfl) => Or.inl rfl | Or.inr (Or.inr h) => Or.inr ((this (h1 :: t1) t2).mpr (Or.inr h))⟩
      rw [merge_preserves, ih _ h1, ih _ h2]
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
      intro i j hi hj hij
      simp [List.get_eq_getElem]
      have h_nodup := remove_duplicates_nodup (filter_common l1 l2)
      have h_sorted := merge_sort_preserves_membership (remove_duplicates (filter_common l1 l2))
      have h_mem := remove_duplicates_preserves_membership (filter_common l1 l2)
      rw [← h_sorted] at hi hj
      have : (merge_sort (remove_duplicates (filter_common l1 l2))).Nodup := by
        sorry -- Need to prove merge_sort preserves nodup
      exact List.nodup_iff_get_ne_get.mp this i j hi hj hij
    · constructor
      · -- is_sorted
        intro i hi
        simp [List.get_eq_getElem]
        sorry -- Need to prove merge_sort produces sorted list
      · -- membership equivalence
        intro i
        simp [merge_sort_preserves_membership, remove_duplicates_preserves_membership, filter_common_spec]